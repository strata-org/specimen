import Specimen.Correctness.SuccObs
import Specimen.Correctness.SizeMeasureExamples
open Basalt
namespace Specimen.Correctness
open Specimen.Correctness.EvSlice

theorem evStepS_sound_succ : StepGenSoundB evStepS (fun _ n => Ev n) := by
  intro prev hprev sz i
  cases i
  show succObs.spec (evStepS prev sz ()) Ev
  unfold evStepS stepBacktrackB evBranchesS
  have hp : ∀ m, succObs.spec (prev m ()) Ev := fun m => hprev m ()
  cases sz with
  | zero => walk; exact Ev.z
  | succ n =>
    walk [hp n]
    · exact Ev.z
    · exact Ev.ss ‹_›
end Specimen.Correctness

#print axioms Specimen.Correctness.evStepS_sound_succ
