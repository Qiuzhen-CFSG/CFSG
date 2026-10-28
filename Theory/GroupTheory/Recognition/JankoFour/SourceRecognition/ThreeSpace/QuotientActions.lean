module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.RadicalStructure
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Mathlib.GroupTheory.NoncommCoprod
/-!
# The marked normalizer quotient and its action on the special radical

Multiplication identifies the literal source quotients (K/R) × (S/R)
with N_G(Z)/R. Conjugation on R/Z(R) descends through this quotient,
and its two commuting factors retain the original K-action on Z and the
previously constructed S/R ≃ S₅ marking. Every marking has a formula on
original representatives; no tensor equivalence is assumed.

This is the quotient-action interface for the tensor clause in
Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

theorem R_normalized : normalizer (d.space : Set G) ≤ normalizer (d.R : Set G) :=
  (le_inf ((normal_subgroupOf_iff_le_normalizer d.K_le_normalizer).mp d.K_normal)
    d.S_normalized).trans inf_normalizer_le_normalizer_inf

theorem R_le_normalizer : d.R ≤ normalizer (d.space : Set G) :=
  inf_le_left.trans d.K_le_normalizer

theorem R_normal_in_normalizer :
    (d.R.subgroupOf (normalizer (d.space : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer d.R_le_normalizer).mpr d.R_normalized

attribute [local instance] R_normal_in_normalizer R_normal_in_K

theorem R_normal_in_S_intrinsic : (d.R.subgroupOf d.S).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show d.R ≤ d.S from inf_le_right)).mpr
    ((centralizer_le_normalizer _).trans d.R_normalized)

attribute [local instance] R_normal_in_S_intrinsic

/-- Conjugation by the original three-space normalizer on the literal R/Z(R). -/
def radicalAction : normalizer (d.space : Set G) →* MulAut (d.R ⧸ center d.R) :=
  (quotientAut (center d.R)).comp
    (d.R.normalizerMonoidHom.comp (inclusion d.R_normalized))

@[simp] theorem radicalAction_mk (n : normalizer (d.space : Set G)) (r : d.R) :
    d.radicalAction n (QuotientGroup.mk' (center d.R) r) =
      QuotientGroup.mk' (center d.R)
        ⟨(n : G)*(r : G)*(n : G)⁻¹,
          (mem_normalizer_iff.mp (d.R_normalized n.property) r).mp r.property⟩ := by
  exact quotientAut_apply_mk _ _ _

theorem R_le_radicalAction_ker (h : IsTypeJ4 z) :
    d.R.subgroupOf (normalizer (d.space : Set G)) ≤ d.radicalAction.ker := by
  let := d.R_center_quotient_elementary h
  intro n hn
  apply MulEquiv.ext
  intro v
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (center d.R) v
  rw [d.radicalAction_mk]
  change QuotientGroup.mk' (center d.R) ((⟨n.val,hn⟩ : d.R)*r*(⟨n.val,hn⟩ : d.R)⁻¹) = _
  rw [map_mul,map_mul,map_inv,mul_comm (QuotientGroup.mk' (center d.R) (⟨n.val,hn⟩ : d.R)),
    mul_inv_cancel_right]
  rfl

def radicalQuotientAction (h : IsTypeJ4 z) :
    (normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G))) →*
      MulAut (d.R ⧸ center d.R) :=
  QuotientGroup.lift _ d.radicalAction (d.R_le_radicalAction_ker h)

@[simp] theorem radicalQuotientAction_mk (h : IsTypeJ4 z)
    (n : normalizer (d.space : Set G)) :
    d.radicalQuotientAction h (QuotientGroup.mk' _ n) = d.radicalAction n := rfl

variable (h : IsTypeJ4 z)

def KQuotientInNormalizer : (d.K ⧸ d.R.subgroupOf d.K) →*
    (normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G))) :=
  QuotientGroup.map _ _ (inclusion d.K_le_normalizer) (fun _ hn => hn)

def SQuotientInNormalizer : (d.S ⧸ d.R.subgroupOf d.S) →*
    (normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G))) :=
  QuotientGroup.map _ _ (inclusion (centralizer_le_normalizer _)) (fun _ hn => hn)

theorem quotient_factors_commute (h : IsTypeJ4 z) (a : d.K ⧸ d.R.subgroupOf d.K)
    (b : d.S ⧸ d.R.subgroupOf d.S) :
    Commute (d.KQuotientInNormalizer a) (d.SQuotientInNormalizer b) := by
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.K) a
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.S) b
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change ⁅QuotientGroup.mk' _ (inclusion d.K_le_normalizer k),
    QuotientGroup.mk' _ (inclusion (centralizer_le_normalizer _) s)⁆ = 1
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ((d.commutator_K_S_le_twoCore h).trans_eq (d.R_eq_S_twoCore h).symm)
    (commutator_mem_commutator k.property s.property)

def quotientProduct : (d.K ⧸ d.R.subgroupOf d.K) × (d.S ⧸ d.R.subgroupOf d.S) →*
    (normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G))) :=
  MonoidHom.noncommCoprod d.KQuotientInNormalizer (d.SQuotientInNormalizer)
    (d.quotient_factors_commute h)

@[simp] theorem quotientProduct_mk (k : d.K) (s : d.S) :
    d.quotientProduct h (QuotientGroup.mk' _ k,QuotientGroup.mk' _ s) =
      QuotientGroup.mk' _ (⟨(k : G)*(s : G),
        (normalizer (d.space : Set G)).mul_mem (d.K_le_normalizer k.property)
          ((centralizer_le_normalizer _) s.property)⟩ : normalizer (d.space : Set G)) := by
  change QuotientGroup.mk' (d.R.subgroupOf (normalizer (d.space : Set G))) (inclusion d.K_le_normalizer k) *
    QuotientGroup.mk' _ (inclusion (centralizer_le_normalizer _) s) = _
  exact (map_mul _ _ _).symm

theorem quotientProduct_bijective : Function.Bijective (d.quotientProduct h) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    rintro ⟨a,b⟩ hab
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.K) a
    obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.S) b
    have hab' : d.quotientProduct h (QuotientGroup.mk' _ k,QuotientGroup.mk' _ s) = 1 := hab
    rw [d.quotientProduct_mk] at hab'
    have hks : (k : G)*(s : G) ∈ d.R := (QuotientGroup.eq_one_iff
      (N := d.R.subgroupOf (normalizer (d.space : Set G))) _).mp hab'
    have hkS : (k : G) ∈ d.S := by
      simpa only [mul_inv_cancel_right] using d.S.mul_mem hks.2 (d.S.inv_mem s.property)
    have hsK : (s : G) ∈ d.K := by
      simpa only [inv_mul_cancel_left] using d.K.mul_mem (d.K.inv_mem k.property) hks.1
    apply mem_bot.mpr
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff _).mpr ⟨k.property,hkS⟩
    · exact (QuotientGroup.eq_one_iff _).mpr ⟨hsK,s.property⟩
  · intro a
    obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨k,hk,s,hs,he⟩ := d.normalizer_product h n.val n.property
    refine ⟨(QuotientGroup.mk' _ (⟨k,hk⟩ : d.K),QuotientGroup.mk' _ (⟨s,hs⟩ : d.S)),?_⟩
    rw [d.quotientProduct_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext he)

noncomputable def quotientProductEquiv :
    (d.K ⧸ d.R.subgroupOf d.K) × (d.S ⧸ d.R.subgroupOf d.S) ≃*
    (normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G))) :=
  MulEquiv.ofBijective (d.quotientProduct h) (d.quotientProduct_bijective h)

@[simp] theorem quotientProductEquiv_mk (k : d.K) (s : d.S) :
    d.quotientProductEquiv h (QuotientGroup.mk' _ k,QuotientGroup.mk' _ s) =
      QuotientGroup.mk' _ (⟨(k : G)*(s : G),
        (normalizer (d.space : Set G)).mul_mem (d.K_le_normalizer k.property)
          ((centralizer_le_normalizer _) s.property)⟩ : normalizer (d.space : Set G)) :=
  d.quotientProduct_mk h k s

/-- The original K/R and S/R act on the same radical section. -/
def KRadicalAction : (d.K ⧸ d.R.subgroupOf d.K) →* MulAut (d.R ⧸ center d.R) :=
  (d.radicalQuotientAction h).comp d.KQuotientInNormalizer

def SRadicalAction : (d.S ⧸ d.R.subgroupOf d.S) →* MulAut (d.R ⧸ center d.R) :=
  (d.radicalQuotientAction h).comp d.SQuotientInNormalizer

@[simp] theorem KRadicalAction_mk (k : d.K) :
    d.KRadicalAction h (QuotientGroup.mk' _ k) =
      d.radicalAction (inclusion d.K_le_normalizer k) := rfl

@[simp] theorem SRadicalAction_mk (s : d.S) :
    d.SRadicalAction h (QuotientGroup.mk' _ s) =
      d.radicalAction (inclusion (centralizer_le_normalizer _) s) := rfl

theorem radical_factors_commute (a : d.K ⧸ d.R.subgroupOf d.K)
    (b : d.S ⧸ d.R.subgroupOf d.S) :
    Commute (d.KRadicalAction h a) (d.SRadicalAction h b) :=
  (d.quotient_factors_commute h a b).map (d.radicalQuotientAction h)

theorem radical_product_action (a : d.K ⧸ d.R.subgroupOf d.K)
    (b : d.S ⧸ d.R.subgroupOf d.S) :
    d.radicalQuotientAction h (d.quotientProductEquiv h (a,b)) =
      d.KRadicalAction h a * d.SRadicalAction h b :=
  map_mul (d.radicalQuotientAction h) _ _

/-- Retain the S/R marking already constructed from the original pair quotient. -/
noncomputable def SQuotientEquiv : (d.S ⧸ d.R.subgroupOf d.S) ≃* Equiv.Perm (Fin 5) :=
  (d.S_quotient_symmetricFive h).some

/-- The source normalizer quotient, with its original K-action and S-quotient marking. -/
noncomputable def markedNormalizerQuotientEquiv :
    (normalizer (d.space : Set G) ⧸ d.R.subgroupOf (normalizer (d.space : Set G))) ≃*
      MulAut d.space × Equiv.Perm (Fin 5) :=
  (d.quotientProductEquiv h).symm.trans
    ((d.KQuotientEquivAut h).prodCongr (d.SQuotientEquiv h))

@[simp] theorem markedNormalizerQuotientEquiv_product (k : d.K) (s : d.S) :
    d.markedNormalizerQuotientEquiv h
      (QuotientGroup.mk' _ (⟨(k : G)*(s : G),
        (normalizer (d.space : Set G)).mul_mem (d.K_le_normalizer k.property)
          ((centralizer_le_normalizer _) s.property)⟩ : normalizer (d.space : Set G))) =
      (d.KAction k,d.SQuotientEquiv h (QuotientGroup.mk' _ s)) := by
  rw [←d.quotientProductEquiv_mk h k s]
  change ((d.KQuotientEquivAut h).prodCongr (d.SQuotientEquiv h))
    ((d.quotientProductEquiv h).symm (d.quotientProductEquiv h _)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Conjugation in the source factor coordinates; no tensor marking is assumed. -/
noncomputable def markedRadicalAction : MulAut d.space × Equiv.Perm (Fin 5) →*
    MulAut (d.R ⧸ center d.R) :=
  (d.radicalQuotientAction h).comp (d.markedNormalizerQuotientEquiv h).symm.toMonoidHom

theorem markedRadicalAction_product (k : d.K) (s : d.S) :
    d.markedRadicalAction h (d.KAction k,d.SQuotientEquiv h (QuotientGroup.mk' _ s)) =
      d.radicalAction (⟨(k : G)*(s : G),
        (normalizer (d.space : Set G)).mul_mem (d.K_le_normalizer k.property)
          ((centralizer_le_normalizer _) s.property)⟩ : normalizer (d.space : Set G)) := by
  rw [←d.markedNormalizerQuotientEquiv_product h k s]
  exact congrArg (d.radicalQuotientAction h)
    ((d.markedNormalizerQuotientEquiv h).symm_apply_apply _)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
end
