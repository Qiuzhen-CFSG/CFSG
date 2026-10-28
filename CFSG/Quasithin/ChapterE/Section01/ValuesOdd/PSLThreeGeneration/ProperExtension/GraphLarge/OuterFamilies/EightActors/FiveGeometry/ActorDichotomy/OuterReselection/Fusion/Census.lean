module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion.Finite
public import Init.Data.Nat.Bitwise.Lemmas
/-!
# Exhaustive census in the 64-element coordinate model

The mask for a coordinate lists precisely the commuting elements whose square
is one. Every bit of these small tables is checked against the multiplication
formula. Three independent commuting involutions have common mask equal to
one of the eight actor masks, as certified by finite kernel reduction.

An arbitrary eight-element set of commuting involutions contains such an
independent triple: successively avoid sets of size one, two, and four.
It lies in the triple's eight-element common mask, hence equals that actor.
This proves exhaustive coverage without enumerating all subsets of the Sylow.
`Fusion.Carrier.candidate_of_census` applies the result to the literal actors.

Source: the fixed-Sylow calculation supporting Aschbacher--Smith E.1.14(7),
printed p.214. The arithmetic model and original diagnostic lists are documented
in `Fusion.Finite`; the tables here are checked certificates, not assumed data.
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion

def index (a : C) : Fin 64 :=
  ⟨(16 * a.1.1.1.val + 4 * a.1.1.2.val + 2 * a.1.2.toNat + a.2.toNat) % 64,
    Nat.mod_lt _ (by decide)⟩
def masks : Fin 64 → Nat :=
  ![2459708267545390959, 3311419789071, 176609055215375, 28527, 142391050766601, 36425617664361, 143494857386345, 37529424234761, 2459708267545390959, 3311419789071, 176609055215375, 28527, 142391050766601, 36425617664361, 143494857386345, 37529424234761, 1103806595329, 144679241869558017, 257, 257, 1103806595329, 2314851312813998337, 257, 257, 1103806595329, 144679241869558017, 257, 257, 1103806595329, 2314851312813998337, 257, 257, 2459566980301202211, 144598663971651, 35321811059523, 141287244178211, 1103806612805, 177712861816101, 2207613199653, 178816668419397, 2459566980301202211, 144598663971651, 35321811059523, 141287244178211, 1103806612805, 177712861816101, 2207613199653, 178816668419397, 1103806595329, 144679241869558017, 257, 257, 1103806595329, 2314851312813998337, 257, 257, 1103806595329, 144679241869558017, 257, 257, 1103806595329, 2314851312813998337, 257, 257]
def mask (a : C) : Nat := masks (index a)
def codeMask : Fin 8 → Nat := ![176609055212805, 26985, 36425617645857, 2314851312813998337, 144679241869558017, 3311419785987, 3855, 143494857376065]

theorem mask_spec : ∀ a b, (mask a).testBit (index b).val = true ↔
    cmul b b = ce ∧ cmul a b = cmul b a := by decide +kernel

theorem codeMask_spec : ∀ i b, (codeMask i).testBit (index b).val = true ↔
    b ∈ codes i := by decide +kernel

def CertTail (a b : C) : Prop :=
  ∀ c : C, cmul c c = ce → c ∉ ({ce,a,b,cmul a b} : Finset C) →
    cmul a c = cmul c a → cmul b c = cmul c b →
    ∃ i : Fin 8, mask a &&& mask b &&& mask c = codeMask i
instance (a b : C) : Decidable (CertTail a b) := by unfold CertTail; infer_instance

def Cert (a : C) : Prop :=
  cmul a a = ce → a ≠ ce → ∀ b : C, cmul b b = ce →
    b ≠ ce → b ≠ a → cmul a b = cmul b a → CertTail a b
def CertMid (a b : C) : Prop :=
  cmul b b = ce → b ≠ ce → b ≠ a → cmul a b = cmul b a → CertTail a b
instance (a b : C) : Decidable (CertMid a b) := by unfold CertMid; infer_instance
instance (a : C) : Decidable (Cert a) := by
  change Decidable (cmul a a = ce → a ≠ ce → ∀ b : C, CertMid a b)
  infer_instance
theorem checked : ∀ a, Cert a := by decide +kernel

theorem census_from_certificate (hcertificate : ∀ a, Cert a) : Census := by
  intro s hs hsq hcomm
  have hsmall₁ : ({ce} : Finset C).card < s.card := by simp [hs]
  obtain ⟨a,ha,hane⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall₁
  have ha1 : a ≠ ce := by simpa using hane
  have hsmall₂ : ({ce,a} : Finset C).card < s.card := by
    have hle := Finset.card_insert_le ce ({a} : Finset C)
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨b,hb,hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall₂
  have hb1 : b ≠ ce ∧ b ≠ a := by simpa using hbnot
  have hsmall₄ : ({ce,a,b,cmul a b} : Finset C).card < s.card := by
    have h1 := Finset.card_insert_le ce ({a,b,cmul a b} : Finset C)
    have h2 := Finset.card_insert_le a ({b,cmul a b} : Finset C)
    have h3 := Finset.card_insert_le b ({cmul a b} : Finset C)
    simp only [Finset.card_singleton] at h3
    omega
  obtain ⟨c,hc,hcnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall₄
  obtain ⟨i,hi⟩ := hcertificate a (hsq a ha) ha1 b (hsq b hb) hb1.1 hb1.2
    (hcomm a ha b hb) c (hsq c hc) hcnot (hcomm a ha c hc) (hcomm b hb c hc)
  refine ⟨i, Finset.eq_of_subset_of_card_le ?_ (by rw [codes_card,hs])⟩
  intro d hd
  apply (codeMask_spec i d).mp
  rw [← hi, Nat.testBit_and, Nat.testBit_and]
  rw [(mask_spec a d).mpr ⟨hsq d hd,hcomm a ha d hd⟩,
    (mask_spec b d).mpr ⟨hsq d hd,hcomm b hb d hd⟩,
    (mask_spec c d).mpr ⟨hsq d hd,hcomm c hc d hd⟩]
  rfl

/-- Every eight-element set of commuting coordinate involutions is one of
the eight complete actor lists. -/
public theorem census : Census := census_from_certificate checked

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection.Fusion
