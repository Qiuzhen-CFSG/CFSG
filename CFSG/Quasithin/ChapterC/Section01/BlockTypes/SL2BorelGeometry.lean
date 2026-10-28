module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverSylowCommutator
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry
public import Theory.GroupTheory.PResidual.PerfectCentralLift
public import Theory.GroupTheory.PResidual.AbelianKernelLift
public import Theory.GroupTheory.SylowPrimeActors
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupAction.NormalizerGeneratingFixer

/-!
# Natural-block Borel geometry on the full cover

The lifted odd torus moves U modulo its central layer; the Sylow
commutator contains that layer. Thus [U,B]=U. The Borel image modulo U
is two-perfect by central transfer, and the moved abelian kernel lifts
this to B itself. In particular the natural L₂(4) block has the same
Borel behavior as the larger fields.

An automorphism fixing B pointwise has displacement in U. Sylow-coset
averaging makes this displacement an inner cocycle from a B-fixed vector.
Such a vector is central, so the automorphism is trivial. Neither argument
splits the central cover.

Source: Aschbacher--Smith15.1.21(i), printed pp.1097--1098, using I.2.3.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open BenderSuzuki.Converse Matrix.ProjectiveSpecialLinearGroup
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual

private theorem natural_borel_geometry {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) :
    IsPPerfect 2 (normalizer (P : Set L)) ∧
      (blockU L ⊓ centralizer (normalizer (P : Set L) : Set L) ≤ center L) ∧
      ∃ D : Subgroup L, D ≤ normalizer (P : Set L) ∧ Odd (Nat.card D) ∧ D ≠ ⊥ := by
  have hb' := hb
  obtain ⟨hn,hs,F,_,_,hF,_,r,⟨m⟩,hm⟩ := hb'
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2^2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  let f := (pi F).comp m.quotientIso.toMonoidHom
  have hfi : Function.Injective f := (pi_injective (F := F)).comp m.quotientIso.injective
  have hfs : Function.Surjective f := (pi_surjective (F := F)).comp m.quotientIso.surjective
  let q := f.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := hfs.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ hfi,QuotientGroup.ker_mk']
  let U := blockU L
  let B := normalizer (P : Set L)
  have hUB : U ≤ B := blockU_le_core.trans
    ((pCore_isPGroup.le_sylow_of_normal P).trans (P : Subgroup L).le_normalizer)
  let π := QuotientGroup.mk' U
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let qU := f.comp (blockCoreProjection (L := L))
  have hqU : Function.Surjective qU := hfs.comp blockCoreProjection_surjective
  have hkU : qU.ker = (pCore 2 L).map π := by
    rw [MonoidHom.ker_comp_of_injective _ _ hfi,blockCoreProjection_ker]
  have hpU : IsPGroup 2 qU.ker := hkU ▸ pCore_isPGroup.map π
  let : Group.IsPerfect PSL(2,F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect (L ⧸ U) :=
    (hs.quotient_twoPerfect U).isPerfect_of_surjective_pGroup_kernel qU hqU hpU
  let P0 := P.mapSurjective hπ
  have hB0 : B.map π = normalizer (P0 : Set (L ⧸ U)) :=
    P.normalizer_map_surjective π hπ
  have hperfect : IsPPerfect 2 (B.map π) := by
    rw [hB0]
    apply isPPerfect_of_central_pKernel_image qU _
      (hkU ▸ blockU_core_image_le_center) hpU
    · exact (hpU.le_sylow_of_normal P0).trans (P0 : Subgroup (L ⧸ U)).le_normalizer
    · intro hd
      exact P0.not_dvd_index (hd.trans (index_dvd_of_le (P0 : Subgroup (L ⧸ U)).le_normalizer))
    · rw [P0.normalizer_map_surjective qU hqU]
      exact Theory.PSL2.OrdinaryBorel.normalizer_twoPerfect hq4 (P0.mapSurjective hqU)
  let S := P.mapSurjective hq
  obtain ⟨g,_,hg⟩ := sylow_normalizer_conjugate F S
  let Dbar := (complement F).map (MulAut.conj g).toMonoidHom
  have hDbarcard : Nat.card Dbar = Nat.card F - 1 := by
    rw [card_map_of_injective (MulAut.conj g).injective,card_torus]
  have hodd : Odd (Nat.card Dbar) := by
    rw [hDbarcard,hF]
    exact Nat.Even.sub_odd (by omega) (even_two.pow_of_ne_zero (by omega)) odd_one
  obtain ⟨D,hD,_,hcard,_⟩ := q.exists_odd_subgroup_lift hq
    (hker ▸ pCore_isPGroup) Dbar hodd
  have hDB : D ≤ B := by
    have hh : D.map q ≤ B.map q := by
      rw [hD,P.normalizer_map_surjective q hq]
      change Dbar ≤ normalizer (S : Set PSL(2,F))
      rw [←hg]
      exact map_mono le_sup_right
    have hh' := comap_mono (f := q) hh
    have hbq : (B.map q).comap q = B := comap_map_eq_self
      (hker.le.trans ((pCore_isPGroup.le_sylow_of_normal P).trans
        (P : Subgroup L).le_normalizer))
    rw [hbq] at hh'
    exact (le_comap_map q D).trans hh'
  have hDodd : Odd (Nat.card D) := hcard ▸ hodd
  have hDne : D ≠ ⊥ := by
    intro he
    rw [he,card_bot,hDbarcard] at hcard
    omega
  let : IsElementaryAbelian 2 U := hs.elementary
  have hcop : Nat.Coprime (Nat.card D) (Nat.card U) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le (blockU_le_core (L := L))).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hDodd).pow_right k
  have hmove : ⁅U,B⁆ = U := by
    apply le_antisymm (le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal)
    have hdec := eq_commutator_sup_centralizer_of_solvable_coprime U D
      le_normalizer_of_normal inferInstance hcop
    apply hdec.le.trans
    apply sup_le
    · exact commutator_mono le_rfl hDB
    · exact (le_inf inf_le_left (hb.blockU_odd_fixed_le_center D hDodd hDne)).trans
        ((hb.central_layer_le_sylow_commutator P).trans
          (commutator_mono le_rfl (P : Subgroup L).le_normalizer))
  have hkπ : π.ker = U := QuotientGroup.ker_mk' U
  let : IsMulCommutative π.ker := by rw [hkπ]; infer_instance
  refine ⟨isPPerfect_of_abelian_kernel_image π B (by rwa [hkπ]) (by rwa [hkπ]) hperfect,?_,D,hDB,hDodd,hDne⟩
  exact (inf_le_inf_left _ (centralizer_le hDB)).trans
    (hb.blockU_odd_fixed_le_center D hDodd hDne)

/-- The Borel of a natural L₂(2ⁿ) block is two-perfect, including n=2. -/
theorem IsL2EvenBlock.borel_twoPerfect {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) :
    IsPPerfect 2 (normalizer (P : Set L)) :=
  (natural_borel_geometry hb P).1

/-- The Borel fixes only central vectors in the full natural cover. -/
theorem IsL2EvenBlock.blockU_borel_fixed_le_center {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) :
    blockU L ⊓ centralizer (normalizer (P : Set L) : Set L) ≤ center L :=
  (natural_borel_geometry hb P).2.1

/-- The actual lifted Borel contains a nontrivial subgroup of odd order. -/
theorem IsL2EvenBlock.exists_odd_borel_subgroup {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) :
    ∃ D : Subgroup L, D ≤ normalizer (P : Set L) ∧ Odd (Nat.card D) ∧ D ≠ ⊥ :=
  (natural_borel_geometry hb P).2.2

private theorem short_fixer {L : Type*} [Group L] [Finite L]
    (hs : IsShort L) (P : Sylow 2 L) (D : Subgroup L)
    (hPD : (P : Subgroup L) ≤ D) (hUD : blockU L ≤ D)
    (hCD : blockU L ⊓ centralizer (D : Set L) ≤ center L)
    (a : MulAut L) (hf : ∀ x ∈ D, a x = x) : a = 1 := by
  let U := blockU L
  let : IsElementaryAbelian 2 U := hs.elementary
  have hdcore (x : L) : a x * x⁻¹ ∈ pCore 2 L := by
    have hh := hs.centralizer_blockU.le
      (Theory.GroupAction.NormalizerGeneratingFixer.displacement_mem_centralizer U a
        (fun y hy => hf y (hUD hy)) x⁻¹ (by rw [normalizer_eq_top]; trivial))
    simpa only [inv_inv,map_inv,mul_inv_rev] using (pCore 2 L).inv_mem hh
  have hd (x : L) : a x * x⁻¹ ∈ U := by
    have he := DFunLike.congr_fun (hs.quotient_blockU_aut_eq_one a hdcore)
      (QuotientGroup.mk' U x)
    rw [quotientAut_apply_mk] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  let c (x : L) : U := ⟨a x * x⁻¹,hd x⟩
  let ρ : L →* MulAut U := MulAut.conjNormal
  have hc (x y : L) : c (x*y) = c x * ρ x (c y) := by
    apply Subtype.ext
    change a (x*y)*(x*y)⁻¹ = (a x*x⁻¹)*(x*(a y*y⁻¹)*x⁻¹)
    simp only [map_mul,mul_inv_rev]
    group
  obtain ⟨v,hv⟩ := binary_cocycle_trivial_of_sylow ρ c hc
    (fun u => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : L) u.property)) P
    (fun x hx => Subtype.ext (by change a x*x⁻¹=1; rw [hf x (hPD hx),mul_inv_cancel]))
  have hvC : (v : L) ∈ centralizer (D : Set L) := by
    intro x hx
    have he := congrArg Subtype.val (hv x)
    change (x*(v : L)*x⁻¹)*(a x*x⁻¹)=(v : L) at he
    rw [hf x hx,mul_inv_cancel,mul_one] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hvZ : (v : L) ∈ center L := hCD ⟨v.property,hvC⟩
  ext x
  have he := congrArg Subtype.val (hv x)
  change (x*(v : L)*x⁻¹)*(a x*x⁻¹)=(v : L) at he
  rw [mem_center_iff.mp hvZ x,mul_inv_cancel_right] at he
  have he' : a x*x⁻¹=1 := mul_left_cancel (he.trans (mul_one (v : L)).symm)
  exact mul_inv_eq_one.mp he'

/-- An automorphism fixing the Borel pointwise fixes the full natural block. -/
theorem IsL2EvenBlock.borel_fixer {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L)
    (a : MulAut L) (hf : ∀ x ∈ normalizer (P : Set L), a x=x) : a=1 :=
  short_fixer hb.2.1 P _ (P : Subgroup L).le_normalizer
    (blockU_le_core.trans ((pCore_isPGroup.le_sylow_of_normal P).trans (P : Subgroup L).le_normalizer))
    (natural_borel_geometry hb P).2.1 a hf


end CFSG.Quasithin.ChapterC
