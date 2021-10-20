use serde::{Deserialize, Serialize};
use static_assertions::const_assert;

const fn bit_size_of<T>() -> usize {
    core::mem::size_of::<T>() * 8
}

pub type RawTaskTableIndex = u16;
const_assert!(bit_size_of::<RawTaskTableIndex>() >= TaskTableIndex::BIT_WIDTH);

pub type RawGeneration = u8;
const_assert!(bit_size_of::<RawGeneration>() >= Generation::BIT_WIDTH);

pub type RawTaskId = u16;
const_assert!(
    bit_size_of::<RawTaskId>()
        >= (TaskTableIndex::BIT_WIDTH + Generation::BIT_WIDTH)
);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct TaskTableIndex(RawTaskTableIndex);

impl TaskTableIndex {
    const BIT_WIDTH: usize = 10;

    const MIN: RawTaskTableIndex = 0;
    const MAX: RawTaskTableIndex = (1 << Self::BIT_WIDTH) - 1;

    pub const KERNEL: Self = Self(Self::MAX);
    pub const UNBOUND: Self = Self(Self::MAX - 1);

    pub const fn from_raw(raw: RawTaskTableIndex) -> Option<Self> {
        if raw <= Self::MAX {
            Some(Self(raw))
        } else {
            None
        }
    }

    pub const unsafe fn unchecked_from_raw(raw: RawTaskTableIndex) -> Self {
        Self(raw)
    }

    pub const fn as_raw(&self) -> RawTaskTableIndex {
        self.0
    }
}

impl core::fmt::Display for TaskTableIndex {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "TaskTableIndex({})", self.0)
    }
}

/// Type used to track generation numbers.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
#[repr(transparent)]
pub struct Generation(RawGeneration);

impl Generation {
    const BIT_WIDTH: usize =
        bit_size_of::<RawTaskId>() - TaskTableIndex::BIT_WIDTH;

    const MIN: RawGeneration = 0;
    const MAX: RawGeneration = (1 << Self::BIT_WIDTH) - 1;

    pub const fn new() -> Self {
        Self(0)
    }

    pub const fn from_raw(raw: RawGeneration) -> Option<Self> {
        if raw <= Self::MAX {
            Some(Self(raw))
        } else {
            None
        }
    }

    pub const unsafe fn unchecked_from_raw(raw: RawGeneration) -> Self {
        Self(raw)
    }

    pub const fn as_raw(&self) -> RawGeneration {
        self.0
    }

    pub fn next(&self) -> Self {
        if self.0 >= Self::MAX {
            Self(0)
        } else {
            Self(self.0 + 1)
        }
    }
}

impl core::fmt::Display for Generation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Generation({})", self.0)
    }
}

/// Names a particular incarnation of a task.
///
/// A `TaskId` combines two fields, a task index (which can be predicted at
/// compile time) and a task generation number. The generation number begins
/// counting at zero and wraps on overflow. Critically, the generation number of
/// a task is incremented when it is restarted. Attempts to correspond with a
/// task using an outdated generation number will return `DEAD`. This helps
/// provide assurance that your peer has not lost its memory between steps of a
/// multi-step IPC sequence.
///
/// If the IPC can be retried against a fresh instance of the peer, it's
/// reasonable to simply increment the generation number and try again, using
/// `TaskId::next_generation`.
///
/// The task index is in the lower `TaskId::INDEX_BITS` bits, while the
/// generation is in the remaining top bits.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[repr(transparent)]
pub struct TaskId(RawTaskId);

impl TaskId {
    const TASK_TABLE_INDEX_SHIFT: usize = 0;
    const TASK_TABLE_INDEX_MASK: u16 = (1 << TaskTableIndex::BIT_WIDTH) - 1;

    const GENERATION_SHIFT: usize = TaskTableIndex::BIT_WIDTH;
    const GENERATION_MASK: u16 = (1 << Generation::BIT_WIDTH) - 1;

    pub const KERNEL: Self =
        Self::for_index_and_gen(TaskTableIndex::KERNEL, Generation::new());

    /// Fabricates a `TaskId` for a known index and generation number.
    pub const fn for_index_and_gen(
        index: TaskTableIndex,
        gen: Generation,
    ) -> Self {
        let index = index.as_raw();
        let gen = gen.as_raw();

        TaskId(
            ((gen as RawTaskId) << Self::GENERATION_SHIFT)
                | (index as RawTaskId),
        )
    }

    pub const fn from_raw(raw: RawTaskId) -> Self {
        Self(raw)
    }

    pub const fn as_raw(self) -> RawTaskId {
        self.0
    }

    // Extracts the index part of this ID.
    pub fn index(&self) -> TaskTableIndex {
        let index = (self.0 >> Self::TASK_TABLE_INDEX_SHIFT)
            & Self::TASK_TABLE_INDEX_MASK;
        unsafe { TaskTableIndex::unchecked_from_raw(index) }
    }

    /// Extracts the generation part of this ID.
    pub fn generation(&self) -> Generation {
        let gen = ((self.0 >> Self::GENERATION_SHIFT) & Self::GENERATION_MASK)
            as RawGeneration;
        unsafe { Generation::unchecked_from_raw(gen) }
    }

    pub fn next_generation(self) -> Self {
        Self::for_index_and_gen(self.index(), self.generation().next())
    }
}

impl core::fmt::Display for TaskId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "TaskId({}, {})", self.index(), self.generation())
    }
}
