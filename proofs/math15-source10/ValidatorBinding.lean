import OriginalValidator
import CanonicalClosure

namespace Math15Source10

/-- Source 10 stated in the original validator definitions.
OriginalValidator changes only the namespace of those definitions. -/
theorem source10_exact_validator : OriginalValidator.Target10 :=
  source10_verified

theorem source12_exact_validator : OriginalValidator.Target12 :=
  source12_verified

end Math15Source10
#check Math15Source10.source10_exact_validator
#print axioms Math15Source10.source10_exact_validator
#print axioms Math15Source10.source12_exact_validator
