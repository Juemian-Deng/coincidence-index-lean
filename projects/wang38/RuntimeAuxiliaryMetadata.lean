import Wang38Full
import Lean
#print Wang38.Frequency.sumN
#print Wang38.Frequency.sumN._unsafe_rec
#print axioms Wang38.Frequency.sumN
#print axioms Wang38.Frequency.sumN._unsafe_rec
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in #[`Wang38.Frequency.sumN, `Wang38.Frequency.sumN._unsafe_rec] do
    let some ci := env.find? n | throwError "MISSING {n}"
    match ci with
    | .defnInfo d => logInfo m!"DECLARATION_KIND {n} defnInfo SAFETY {repr d.safety}"
    | .opaqueInfo _ => logInfo m!"DECLARATION_KIND {n} opaqueInfo"
    | .thmInfo _ => logInfo m!"DECLARATION_KIND {n} thmInfo"
    | _ => logInfo m!"DECLARATION_KIND {n} other"
    logInfo m!"RUNTIME_FLAGS {n} unsafe={ci.isUnsafe} partial={ci.isPartial}"
    logInfo m!"DIRECT_KERNEL_CONSTANTS {n} {ci.getUsedConstantsAsSet.toArray.qsort Name.lt}"
