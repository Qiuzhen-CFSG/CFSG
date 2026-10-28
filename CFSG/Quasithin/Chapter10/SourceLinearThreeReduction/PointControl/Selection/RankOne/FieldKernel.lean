module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.OddFixedLayer
public import Theory.Representation.SL2NaturalOffenders.FieldKernel

/-!
# The residual field action on the original rank-one fixed layer

The natural quotient embeds the local moved-module automizer in its literal
binary linear normalizer. The semilinear coefficient homomorphism detects
all two-elements outside the marked SL₂ image. Trivial coefficient action
therefore fixes the original moved kernel, using equality of the full and
quotient action kernels.

For any local two-subgroup normalizing L, its commutator fixes that kernel,
and a power of two dividing the marked field degree kills its remaining
action. The half-Sylow is normal in T, so conjugation by the specified
exchanger transfers the same bounds to both moved kernels and hence the
whole L₀-fixed layer. No assertion that the field action vanishes is used.
The application to the original minimal source setup is in ModuleChoice.Source.

Source: Aschbacher--Smith B.4.2(1), 10.1.1(1), and the point argument in
10.2.9, printed pp.86,741,750. The ambient even-degree fixation and quiet
support obligations remain with qt-d-10-nona5-point-selection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
  (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

include e c

/-- The literal moved-kernel action of a local two-subgroup is controlled by
the coefficient homomorphism of the marked natural quotient. -/
theorem exists_two_subgroup_kernel_field_control
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G)) :
    ∃ φ : P →* (F ≃+* F),
      ∀ a : P, φ a = 1 → (a : G) ∈ centralizer (sourceMovedFixed D : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let M := D.maximalLocal ⊓ normalizer (L : Set G)
  let N := M ⊓ normalizer (W : Set G)
  let q := localNormalizerAction W M
  let σ := SL2.BinarySmall.natural (K := F)
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hLM : L ≤ M := le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  have hNL : N ≤ normalizer (L : Set G) := inf_le_left.trans inf_le_right
  have hNZ := (le_inf hNL (show N ≤ normalizer (W : Set G) from inf_le_right)).trans
    (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage N W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    have hh : commutatorPreimage N W (sourceMovedFixed D) ≤
        commutatorPreimage (normalizer (L : Set G) ⊓ normalizer (W : Set G)) W (sourceMovedFixed D) :=
      le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans (le_inf hNL inf_le_right))
        (commutator_commutatorPreimage_le _ _ _ hNZ)
    rw [moved_normalizer_quotient_kernel D e c] at hh
    exact hh.trans inf_le_right
  obtain ⟨τ,ι,hι,hιτ,hact⟩ := exists_local_section_normalizer L W (sourceMovedFixed D) M
    σ π hπ c hLM hNL hNZ hk
  have hLN : L ≤ N := le_inf hLM c.normalized
  have hPW : P ≤ normalizer (W : Set G) := by
    intro p hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj p).toMonoidHom = ⁅D.fullModule,L⁆
    have hV : D.fullModule.map (MulAut.conj p).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hPM hp))
    have hL : L.map (MulAut.conj p).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (hPL hp)
    rw [map_commutator,hV,hL]
  have hPN : P ≤ N := le_inf (le_inf hPM hPL) hPW
  have hmark (l : L) : τ (q (inclusion hLN l)) = σ (π l) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := c.onto (Multiplicative.ofAdd v)
    exact (hact (inclusion hLN l) w).trans (c.equivariant l w)
  obtain ⟨φ,hφ⟩ := SL2NaturalOffenders.exists_natural_normalizer_field_control (F := F)
  let j : P →* N := inclusion hPN
  refine ⟨φ.comp (ι.comp (q.comp j)),?_⟩
  intro a hfield
  let aN : N := j a
  have hpow : ∃ k : ℕ, (ι (q aN)) ^ (2 ^ k) = 1 := by
    obtain ⟨k,hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hP) a
    refine ⟨k,?_⟩
    have hk' : aN ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      exact congrArg (fun x : P => (x : G)) hk
    rw [←map_pow,←map_pow,hk',map_one,map_one]
  obtain ⟨g,hg⟩ := hφ (ι (q aN)) hpow hfield
  have hg' : τ (q aN) = σ g := by
    have hh := congrArg (fun x : (Module.End (ZMod 2) (Fin 2 → F))ˣ => x.val) hg
    exact (LinearMap.ext (fun v => (hιτ (q aN) v).symm)).trans hh.symm
  obtain ⟨l,hl⟩ := hπ g
  have he : q aN = q (inclusion hLN l) := by
    apply hι
    apply Subtype.ext
    apply Units.ext
    calc
      (ι (q aN)).val.val = τ (q aN) := LinearMap.ext (fun v => hιτ (q aN) v)
      _ = σ g := hg'
      _ = σ (π l) := (congrArg σ hl).symm
      _ = τ (q (inclusion hLN l)) := (hmark l).symm
      _ = (ι (q (inclusion hLN l))).val.val := LinearMap.ext (fun v => (hιτ _ v).symm)
  have hc : (a : G) * (l : G)⁻¹ ∈ centralizer (W : Set G) := by
    apply (localNormalizerAction_eq_one_iff W M (aN * (inclusion hLN l)⁻¹)).mp
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hm := (L ⊔ centralizer (W : Set G)).mul_mem
    ((show centralizer (W : Set G) ≤ L ⊔ centralizer (W : Set G) from le_sup_right) hc)
    ((show L ≤ L ⊔ centralizer (W : Set G) from le_sup_left) l.property)
  have hmem : (a : G) ∈ L ⊔ centralizer (W : Set G) := by
    simpa only [inv_mul_cancel_right] using hm
  exact (sup_le
    (le_centralizer_iff.mp (show sourceMovedFixed D ≤ centralizer (L : Set G) from inf_le_right))
    (centralizer_le inf_le_left)) hmem

/-- The original kernel action is abelian, and is killed by a power of two
dividing the original field degree. No zero-kernel or odd-degree premise is used. -/
theorem two_subgroup_kernel_field_bound
    {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPM : P ≤ D.maximalLocal) (hPL : P ≤ normalizer (L : Set G)) :
    ⁅P,P⁆ ≤ centralizer (sourceMovedFixed D : Set G) ∧
      ∃ k : ℕ, 2 ^ k ∣ n ∧
        ∀ a ∈ P, a ^ (2 ^ k) ∈ centralizer (sourceMovedFixed D : Set G) := by
  obtain ⟨φ,hφ⟩ := exists_two_subgroup_kernel_field_control D e c P hP hPM hPL
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun f : F ≃+* F => (f : F → F)) DFunLike.coe_injective
  let : IsCyclic (F ≃+* F) := SL2NaturalOffenders.binaryFieldAut_isCyclic
  have hp : IsPGroup 2 φ.range := hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hd : 2 ^ k ∣ n := by
    rw [←hk,←FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hcard]
    exact φ.range.card_subgroup_dvd_card
  refine ⟨?_,k,hd,?_⟩
  · rw [←P.map_subtype_commutator]
    rintro _ ⟨a,ha,rfl⟩
    exact hφ a (Abelianization.commutator_subset_ker φ ha)
  · intro a ha
    change (((⟨a,ha⟩ : P) ^ (2 ^ k) : P) : G) ∈ centralizer (sourceMovedFixed D : Set G)
    apply hφ ((⟨a,ha⟩ : P) ^ (2 ^ k))
    change φ ((⟨a,ha⟩ : P) ^ (2 ^ k)) = 1
    rw [map_pow]
    have hh := pow_card_eq_one' (x := φ.rangeRestrict (⟨a,ha⟩ : P))
    rw [hk] at hh
    exact congrArg Subtype.val hh

omit e c in
include D in
private theorem half_sylow_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer
      (↑((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi : (S.subgroupOf (T : Subgroup G)).index = 2 := by
    have he : S.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp (normal_of_index_eq_two hi)

/-- The whole original fixed layer is fixed by the half-Sylow commutator.
Its remaining action has two-power exponent dividing the specified field degree. -/
theorem half_sylow_fixed_layer_field_bound
    {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
    let Z := D.fullModule ⊓ centralizer (localOrbit T L : Set G)
    ⁅S,S⁆ ≤ centralizer (Z : Set G) ∧
      ∃ k : ℕ, 2 ^ k ∣ n ∧ ∀ a ∈ S, a ^ (2 ^ k) ∈ centralizer (Z : Set G) := by
  dsimp only
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let K := sourceMovedFixed D
  have hTS := half_sylow_normalized D (fun hn => htn (hn ht))
  have hmap : S.map (MulAut.conj t).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS ht)
  obtain ⟨hderived,k,hk,hpow⟩ := two_subgroup_kernel_field_bound D e c hcard S
    (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
  rw [BinaryThree.fixed_layer_eq_moved_kernels D ht htn hcross]
  constructor
  · have hother := map_mono (f := (MulAut.conj t).toMonoidHom) hderived
    rw [map_commutator,hmap,Theory.GroupTheory.map_centralizer_equiv] at hother
    exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hderived)
      (le_centralizer_iff.mp hother))
  · refine ⟨k,hk,fun a ha => ?_⟩
    have hinv : (MulAut.conj t⁻¹) a ∈ S :=
      (mem_normalizer_iff.mp (hTS ((T : Subgroup G).inv_mem ht)) a).mp ha
    have hh := mem_map_of_mem (MulAut.conj t).toMonoidHom (hpow _ hinv)
    rw [Theory.GroupTheory.map_centralizer_equiv] at hh
    have hother : a ^ (2 ^ k) ∈ centralizer
        (K.map (MulAut.conj t).toMonoidHom : Set G) := by
      simpa only [K,Subgroup.coe_map,MulEquiv.coe_toMonoidHom,map_pow,MulAut.conj_apply,inv_inv,
        mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh
    have hjoin : K ⊔ K.map (MulAut.conj t).toMonoidHom ≤
        centralizer ({a ^ (2 ^ k)} : Set G) :=
      sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hpow a ha v hv))
        (fun v hv => mem_centralizer_singleton_iff.mpr (hother v hv))
    exact fun v hv => mem_centralizer_singleton_iff.mp (hjoin hv)

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
