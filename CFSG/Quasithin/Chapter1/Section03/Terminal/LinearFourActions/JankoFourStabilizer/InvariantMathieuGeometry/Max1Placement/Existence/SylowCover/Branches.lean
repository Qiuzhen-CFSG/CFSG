module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Recognizing the central and large elementary J₄ Sylow overgroups

For a maximal subgroup M containing an ambient Sylow two-subgroup S, a normal
subgroup of order two is central. Sylow conjugacy and the certified center of
a Sylow subgroup of C(a) identify its nonidentity element with a conjugate
of a. Maximality then identifies M with that full centralizer. The certified
max2 generation theorem provides the actual isomorphism with the original
ATLAS word subgroup.

If instead M has a normal elementary subgroup of order at least 2048, align
a Sylow of the literal max1 subgroup with S using its proved odd index.
The finite quotient-action bound makes the transported elementary subgroup
exactly the literal Mathieu kernel. Its proved ambient normalizer puts M
inside that conjugate of max1, so maximality gives equality. The order-37
word proves max1 is proper. Neither argument assumes ambient simplicity.

These are two branches of the normal-elementary reduction; they do not
assert existence of either normal subgroup in an arbitrary M. Source context:
Aschbacher–Smith A.3.12 and its Sylow-overgroup proof, printed pp.47–48,
citing Aschbacher, *Overgroups of Sylow subgroups in sporadic groups* (1986).
GLS3 Table 5.3i records the relevant local groups. The imported matrix,
Sylow-center, kernel-action, and normalizer certificates discharge the actual
model facts used here; no table entry is used as a proof premise.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Janko4.Cardinality Janko4.LocalStructure
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] Janko4.modelGroup matrixA matrixB max1Subgroup localKernel

private noncomputable def sourceEquivCentralizer :
    sourceSubgroup ≃* centralizer ({Janko4.a} : Set Model) :=
  sourceSubgroupEquivLocal.trans
    (((MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv).trans
      ((MonoidHom.ofInjective centralizerToModel_injective).trans
        (MulEquiv.subgroupCongr centralizerToModel_range)))

private theorem centralizer_a_ne_top : centralizer ({Janko4.a} : Set Model) ≠ ⊤ := by
  intro h
  exact a_mul_b_ne_b_mul_a
    (mem_centralizer_singleton_iff.mp (h ▸ mem_top Janko4.b)).symm

private theorem central_sylow_involution_conjugate
    (S : Sylow 2 Model) (z : Model) (hzS : z ∈ S)
    (hzc : ∀ s : Model, s ∈ S → s * z = z * s) (hz : z ≠ 1) :
    ∃ g : Model, (MulAut.conj g) Janko4.a = z := by
  classical
  let C := centralizer ({Janko4.a} : Set Model)
  let P : Sylow 2 C := default
  obtain ⟨T, hT⟩ := Janko4.OuterReduction.OddIndex.centralizer_sylow_is_ambient P
  have hcenter : (center T).map T.toSubgroup.subtype = zpowers Janko4.a := by
    rw [hT]
    exact Janko4.OuterReduction.OddIndex.centralizer_sylow_center P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T S
  have hTS : T.toSubgroup.map (MulAut.conj g).toMonoidHom = S.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  have hzT : (MulAut.conj g).symm z ∈ T := by
    have hm : z ∈ T.toSubgroup.map (MulAut.conj g).toMonoidHom := by
      rw [hTS]
      exact hzS
    obtain ⟨x, hx, rfl⟩ := hm
    change (MulAut.conj g).symm ((MulAut.conj g) x) ∈ T.toSubgroup
    rw [MulEquiv.symm_apply_apply]
    exact hx
  have hzcenter : (⟨(MulAut.conj g).symm z, hzT⟩ : T) ∈ center T := by
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    apply (MulAut.conj g).injective
    have htS : (MulAut.conj g) t ∈ S.toSubgroup := by
      rw [← hTS]
      exact mem_map_of_mem _ t.property
    change (MulAut.conj g) ((t : Model) * (MulAut.conj g).symm z) =
      (MulAut.conj g) ((MulAut.conj g).symm z * (t : Model))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      hzc ((MulAut.conj g) t) htS
  have hm : (MulAut.conj g).symm z ∈ zpowers Janko4.a :=
    hcenter ▸ mem_map_of_mem T.toSubgroup.subtype hzcenter
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_a] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hn' : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · have he' : (MulAut.conj g).symm z = 1 := by simpa using he.symm
    exact (hz ((MulAut.conj g).symm.injective
      (he'.trans (map_one _).symm))).elim
  · refine ⟨g, ?_⟩
    have he' : (MulAut.conj g).symm z = Janko4.a := by simpa using he.symm
    exact (congrArg (MulAut.conj g) he').symm.trans
      ((MulAut.conj g).apply_symm_apply z)

/-- A normal subgroup of order two identifies the maximal Sylow overgroup
with the original max2 carrier, with no simplicity assumption. -/
theorem normal_two_recognition (S : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    (E : Subgroup M) [E.Normal] (hE : Nat.card E = 2) :
    Nonempty (M ≃* sourceSubgroup) := by
  obtain ⟨z, hzne, _⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hE
  let zm : M := z
  have hzm : zm ≠ 1 := fun h => hzne (Subtype.ext h)
  have hz : (zm : Model) ≠ 1 := fun h => hzm (Subtype.ext h)
  have hp : IsPGroup 2 E := IsPGroup.of_card (n := 1) (by simpa using hE)
  have hzS : (zm : Model) ∈ S := (hp.le_sylow_of_normal (S.subtype hSM)) z.property
  have hzc : zm ∈ center M := central_of_normal_card_two E hE z.property
  have hMC : M ≤ centralizer ({(zm : Model)} : Set Model) := by
    intro m hm
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun x : M => (x : Model)) (mem_center_iff.mp hzc ⟨m, hm⟩))
  obtain ⟨g, hg⟩ := central_sylow_involution_conjugate S zm hzS
    (fun s hs => mem_centralizer_singleton_iff.mp (hMC (hSM hs))) hz
  have hC : (centralizer ({Janko4.a} : Set Model)).map (MulAut.conj g).toMonoidHom =
      centralizer ({(zm : Model)} : Set Model) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, hg] using
        map_centralizer_le_centralizer_image ({Janko4.a} : Set Model)
          (MulAut.conj g).toMonoidHom
    · intro x hx
      refine ⟨(MulAut.conj g).symm x, mem_centralizer_singleton_iff.mpr ?_,
        (MulAut.conj g).apply_symm_apply x⟩
      apply (MulAut.conj g).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply, hg] using
        mem_centralizer_singleton_iff.mp hx
  have hproper : centralizer ({(zm : Model)} : Set Model) ≠ ⊤ := by
    intro ht
    apply centralizer_a_ne_top
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hC, ht, map_top_of_surjective _ (MulAut.conj g).surjective]
  have heq : centralizer ({(zm : Model)} : Set Model) = M :=
    (hM.le_iff_eq hproper).mp hMC
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans
    (((MulEquiv.subgroupCongr hC).symm.trans
      ((MulAut.conj g).subgroupMap (centralizer ({Janko4.a} : Set Model))).symm).trans
        sourceEquivCentralizer.symm)⟩

private theorem max1_ne_top : SylowCore.Local ≠ (⊤ : Subgroup Model) := by
  intro h
  have hd : 37 ∣ Nat.card SylowCore.Local := by
    have ha : Janko4.a * Janko4.b ∈ SylowCore.Local := h ▸ mem_top _
    have hd := orderOf_dvd_natCard (⟨Janko4.a * Janko4.b, ha⟩ : SylowCore.Local)
    rwa [← orderOf_coe, orderOf_a_mul_b] at hd
  rw [max1Subgroup_card] at hd
  norm_num at hd

/-- The literal local Sylow can be aligned with any supplied ambient Sylow. -/
private theorem max1_sylow_alignment (S : Sylow 2 Model) :
    ∃ (P : Sylow 2 SylowCore.Local) (g : Model),
      P.toSubgroup.map ((MulAut.conj g).toMonoidHom.comp SylowCore.Local.subtype) =
        S.toSubgroup := by
  let P : Sylow 2 SylowCore.Local := default
  have hi : ¬ 2 ∣ (P.toSubgroup.map SylowCore.Local.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two P.not_dvd_index
      Janko4.OuterReduction.max1_odd_index_unconditional
  let T := (P.isPGroup'.map SylowCore.Local.subtype).toSylow hi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T S
  refine ⟨P, g, ?_⟩
  rw [← map_map]
  exact congrArg Sylow.toSubgroup hg

/-- A normal elementary subgroup of order at least 2048 forces the literal Mathieu
branch. The uniqueness bound is used on the actual aligned Sylow subgroup. -/
theorem normal_large_recognition (S : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    (E : Subgroup M) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : 2048 ≤ Nat.card E) : Nonempty (M ≃* certifiedMathieuSubgroup) := by
  obtain ⟨P, g, hPS⟩ := max1_sylow_alignment S
  let j : SylowCore.Local →* Model :=
    (MulAut.conj g).toMonoidHom.comp SylowCore.Local.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp Subtype.val_injective
  let f : P →* M := (j.comp P.toSubgroup.subtype).codRestrict M (by
    intro p
    apply hSM
    rw [← hPS]
    exact mem_map_of_mem _ p.property)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hj (congrArg Subtype.val hxy))
  have hEP : E ≤ (S.subtype hSM).toSubgroup :=
    (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal _
  have hErange : E ≤ f.range := by
    intro e he
    have heS : (e : Model) ∈ S.toSubgroup := hEP he
    rw [← hPS] at heS
    obtain ⟨p, hp, heq⟩ := heS
    exact ⟨⟨p, hp⟩, Subtype.ext heq⟩
  let A : Subgroup P := E.comap f
  let eA : A ≃* E := MulEquiv.ofBijective (f.subgroupComap E) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hf (congrArg Subtype.val hxy))
    · intro e
      obtain ⟨p, hp⟩ := hErange e.property
      refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
      change f p ∈ E
      rw [hp]
      exact e.property)
  have hAelem : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun x y => eA.injective
      ((eA.map_mul x y).trans ((mul_comm _ _).trans (eA.map_mul y x).symm))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      eA.injective (by
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) (eA x))) }
  let := hAelem
  have hAcard : 2048 ≤ Nat.card A := hE.trans_eq (Nat.card_congr eA.toEquiv).symm
  have hA : A = SylowCore.core P :=
    localKernel_sylow_unique_of_quotientCentralizerBound
      (SylowCore.quotientCentralizerBound_of_fixedBound SylowCore.normalElementaryFixedBound)
      P A hAcard
  have hmaps : (E.map M.subtype) =
      (localKernel matrixA_mul_self matrixB_pow_four).map j := by
    have hAf : A.map f = E := by
      exact map_comap_eq_self hErange
    have heq := congrArg (fun K : Subgroup M => K.map M.subtype) hAf
    rw [map_map] at heq
    have hcomp : M.subtype.comp f = j.comp P.toSubgroup.subtype := rfl
    rw [hcomp, ← map_map, hA, map_subgroupOf_eq_of_le (localKernel_le_sylow P)] at heq
    exact heq.symm
  have hMN : M ≤ normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map j : Set Model) := by
    rw [← hmaps]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map M.subtype
  have hN : normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map j : Set Model) ≤
      SylowCore.Local.map (MulAut.conj g).toMonoidHom := by
    change normalizer ((localKernel matrixA_mul_self matrixB_pow_four).map
      ((MulAut.conj g).toMonoidHom.comp SylowCore.Local.subtype) : Set Model) ≤ _
    rw [← map_map, ← map_equiv_normalizer_eq]
    exact map_mono normalizer_embedded_localKernel_le_max1
  have hproper : SylowCore.Local.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro ht
    apply max1_ne_top
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [ht, map_top_of_surjective _ (MulAut.conj g).surjective]
  have heq : SylowCore.Local.map (MulAut.conj g).toMonoidHom = M :=
    (hM.le_iff_eq hproper).mp (hMN.trans hN)
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans
    ((MulAut.conj g).subgroupMap SylowCore.Local).symm⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
