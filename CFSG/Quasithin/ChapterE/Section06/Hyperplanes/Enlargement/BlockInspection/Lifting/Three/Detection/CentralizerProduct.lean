module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.FactorAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.AlternatingTransport
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.LinearTransport
public import Theory.GroupAction.FixedCoatomDisplacement
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Assembling the envelope centralizer product from factor transporters

First C_M(U) centralizes V: its induced action fixes a hyperplane and
therefore has exponent two, while the obstruction residual condition
kills a Sylow two-subgroup of that image.

Write an element of C_R(U) as m times a product of E.6.7 factors.
The TI hypothesis makes m normalize V, so the latter product transports
U into V. Split off each factor with a companion centralizing it.
Once the moved coordinates lie in M, collect them there and leave only
the factors centralized by U. The first paragraph then replaces the
remaining M-coordinate by an element of C_R(V).

The alternating transporter uses the actual rank-one V-action and lifts
fixedness through the center using the common Sylow subgroup. The natural
transporter uses the corank-two bound to reduce to L₂(4), then places its
coordinate in the marked Borel. Splitting the chi-zero alternatives
discharges every factor premise and proves `EnvelopeCentralizerProduct`
from Hypothesis E.6.1 and the permitted earlier odd-core conclusion.
In particular no centralizer is distributed over a product.
Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
E.6.7 and E.6.23, printed pp.246 and 254–255; C.1.7–13, pp.123–125.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

/-- The M-intersection contributes only elements centralizing all of V. -/
theorem local_hyperplane_centralizer_le
    {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hUh : IsHyperplane V U) : M ⊓ centralizer (U : Set G) ≤ centralizer (V : Set G) := by
  let _ := h.elementary
  let C := M ⊓ centralizer (U : Set G)
  have hCN := h.localCentralizer_le_normalizer hU.2.1 hU.1
  let f : C →* MulAut V := V.normalizerMonoidHom.comp (inclusion hCN)
  have hi : (U.subgroupOf V).index = 2 := by
    change U.relIndex V = 2
    calc
      U.relIndex V = 2 ^ subgroupCorank V U := by
        rw [subgroupCorank_eq_quotient_finrank]
        exact Subgroup.relIndex_eq_two_pow_quotient_finrank V U
      _ = 2 := by rw [hUh.2]; rfl
  have hsq (c : C) : (f c) ^ 2 = 1 := by
    apply MulAut.square_eq_one_of_fixed_index_dvd_two
    rw [← hi]
    apply index_dvd_of_le
    intro u hu a
    obtain ⟨n, hn⟩ := a.property
    change (a : MulAut V) • u = u
    rw [← hn]
    apply MulAction.mem_fixedBy_zpow
    apply Subtype.ext
    change (c : G) * (u : G) * (c : G)⁻¹ = u
    rw [← mem_centralizer_iff.mp c.property.2 u hu, mul_inv_cancel_right]
  have hp : IsPGroup 2 f.range := isPGroup_iff_pow_pow_eq_one.mpr (by
    rintro ⟨_, c, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hsq c)⟩)
  let S : Sylow 2 C := Classical.arbitrary _
  let P := S.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have htop : (P : Subgroup f.range) = ⊤ :=
    (P.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  intro x hx
  have hf : f ⟨x, hx⟩ = 1 := by
    have hm : f.rangeRestrict ⟨x, hx⟩ ∈ (S : Subgroup C).map f.rangeRestrict := by
      change _ ∈ (P : Subgroup f.range)
      rw [htop]
      trivial
    obtain ⟨s, hs, he⟩ := hm
    have hsV : (s : G) ∈ centralizer (V : Set G) :=
      hU.2.2.2.two_subgroup_centralizes (S.isPGroup'.map C.subtype)
        (map_subtype_le _) (mem_map_of_mem _ hs)
    have hfs : f s = 1 := by
      change V.normalizerMonoidHom ⟨s, hCN s.property⟩ = 1
      rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
      exact hsV
    exact (congrArg Subtype.val he).symm.trans hfs
  have hk : (⟨x, hCN hx⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker := hf
  rwa [normalizerMonoidHom_ker] at hk


omit [Finite G] in
private theorem factorProduct_mem {I : Type*} [Fintype I] {B : I → Subgroup G}
    (hc : Pairwise fun i j => ∀ x y : G, x ∈ B i → y ∈ B j → Commute x y)
    (f : ∀ i, B i) (N : Subgroup G) (hf : ∀ i, (f i : G) ∈ N) :
    noncommPiCoprod hc f ∈ N := by
  rw [noncommPiCoprod_apply]
  exact N.noncommProd_mem _ (fun i _ => hf i)

omit [Finite G] in
private theorem centralizing_product_transporter
    {Q M V A R U : Subgroup G} (d : E67Decomposition Q M V A R)
    (hmoved : ∀ i, ¬ d.block i ≤ centralizer (U : Set G) →
      FactorTransporter (d.block i) M U V)
    (b : G) (hb : b ∈ ⨆ i, d.block i)
    (htrans : U.map (MulAut.conj b).toMonoidHom ≤ V) :
    ∃ m ∈ M, ∃ z ∈ fixedFactorJoin d U, m * z = b := by
  classical
  have hc : Pairwise fun i j => ∀ x y : G,
      x ∈ d.block i → y ∈ d.block j → Commute x y := by
    intro i j hij x y hx hy
    exact (mem_centralizer_iff.mp (d.commuting i j hij hy) x hx)
  let p := noncommPiCoprod hc
  have hpr : p.range = ⨆ i, d.block i := noncommPiCoprod_range
  obtain ⟨f, rfl⟩ := hpr ▸ hb
  have hiM (i : Fin d.count) (hi : ¬ d.block i ≤ centralizer (U : Set G)) :
      (f i : G) ∈ M := by
    let r : ∀ j, d.block j := fun j => if j = i then 1 else f j
    have he : Pi.mulSingle i (f i) * r = f := by
      funext j
      by_cases hj : j = i
      · subst j; simp [r]
      · simp [r, hj]
    have hprod : (f i : G) * p r = p f := by
      calc
        (f i : G) * p r = p (Pi.mulSingle i (f i) * r) := by
          rw [map_mul, noncommPiCoprod_mulSingle]
        _ = p f := congrArg p he
    have hr : p r ∈ centralizer (d.block i : Set G) := by
      apply factorProduct_mem hc r
      intro j
      by_cases hj : j = i
      · subst j; simpa only [r, if_pos rfl, Subgroup.coe_one] using (centralizer (d.block i : Set G)).one_mem
      · exact d.commuting i j (Ne.symm hj) (r j).property
    exact hmoved i hi (f i) (f i).property (p r) hr (by rwa [hprod])
  let fm : ∀ i, d.block i := fun i =>
    if d.block i ≤ centralizer (U : Set G) then 1 else f i
  let fd : ∀ i, d.block i := fun i =>
    if d.block i ≤ centralizer (U : Set G) then f i else 1
  refine ⟨p fm, ?_, p fd, ?_, ?_⟩
  · apply factorProduct_mem hc fm
    intro i
    by_cases hi : d.block i ≤ centralizer (U : Set G)
    · simp [fm, hi]
    · simpa [fm, hi] using hiM i hi
  · apply factorProduct_mem hc fd
    intro i
    by_cases hi : d.block i ≤ centralizer (U : Set G)
    · exact (le_iSup (fun j : FixedFactors d U => d.block j.val) ⟨i, hi⟩)
        (by simp [fd, hi])
    · simp [fd, hi]
  · rw [← map_mul]
    congr 1
    funext i
    by_cases hi : d.block i ≤ centralizer (U : Set G) <;> simp [fm, fd, hi]

/-- Factor transporters and the genuine obstruction hypotheses imply the set product. -/
theorem centralizer_product_of_factorTransporters
    {K : GroupClass} {T : Sylow 2 G} {M V A R U : Subgroup G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hUh : IsHyperplane V U) (hA : A ∈ obstructionFamily M V)
    (hRA : R ≤ centralizer (A : Set G))
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A R)
    (hmoved : ∀ i, ¬ d.block i ≤ centralizer (U : Set G) →
      FactorTransporter (d.block i) M U V) :
    ((R ⊓ centralizer (U : Set G) : Subgroup G) : Set G) =
      ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G) *
        (fixedFactorJoin d U : Set G) := by
  have hDR : fixedFactorJoin d U ≤ R := iSup_le fun i => d.le i.val
  have hDU : fixedFactorJoin d U ≤ centralizer (U : Set G) :=
    iSup_le fun i => i.property
  have hMRN : R ⊓ M ≤ normalizer (V : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hRA)).trans
      (h.localCentralizer_le_normalizer hA.2.1 hA.1)
  apply Set.Subset.antisymm
  · rintro x ⟨hxR, hxU⟩
    obtain ⟨m, hm, b, hb, he⟩ := d.product ▸ hxR
    have htrans : U.map (MulAut.conj b).toMonoidHom ≤ V := by
      rintro _ ⟨u, hu, rfl⟩
      have heq : b * u * b⁻¹ = m⁻¹ * u * m := by
        have hh := mem_centralizer_iff.mp hxU u hu
        rw [← he] at hh
        calc
          b * u * b⁻¹ = m⁻¹ * ((m * b) * u) * b⁻¹ := by group
          _ = m⁻¹ * (u * (m * b)) * b⁻¹ := by rw [hh]
          _ = m⁻¹ * u * m := by group
      change b * u * b⁻¹ ∈ V
      rw [heq]
      exact (mem_normalizer_iff''.mp (hMRN hm) u).mp (hU.1 hu)
    obtain ⟨m', hm', z, hz, hb'⟩ := centralizing_product_transporter d hmoved b hb htrans
    have hx : (m * m') * z = x := by rw [mul_assoc, hb']; exact he
    have hmc : m * m' ∈ R ⊓ centralizer (U : Set G) := by
      have hh := (R ⊓ centralizer (U : Set G)).mul_mem ⟨hxR, hxU⟩
        ((R ⊓ centralizer (U : Set G)).inv_mem ⟨hDR hz, hDU hz⟩)
      rwa [← hx, mul_inv_cancel_right] at hh
    exact ⟨m * m', ⟨hmc.1, local_hyperplane_centralizer_le h hU hUh
      ⟨M.mul_mem hm.2 hm', hmc.2⟩⟩, z, hz, hx⟩
  · rintro x ⟨c, hc, z, hz, rfl⟩
    exact ⟨R.mul_mem hc.1 (hDR hz), (centralizer (U : Set G)).mul_mem
      (centralizer_le hU.1 hc.2) (hDU hz)⟩

/-- Generic envelope assembly from coordinate transporter statements. -/
theorem envelopeCentralizerProduct_of_factorTransporters
    {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 K T M V)
    (htransport : ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
      ∀ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
        (layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V)),
      ∀ i, ¬ d.block i ≤ centralizer (U : Set G) →
        FactorTransporter (d.block i) M U V) : EnvelopeCentralizerProduct T M V := by
  intro U hU hUh A hA hAU hc d
  apply centralizer_product_of_factorTransporters h hU hUh hA
    (layerEnvelope_le (inf_le_right.trans (centralizer_le hA.1))) d
  exact htransport U hU hUh A hA hAU hc d

/-- The exact envelope set product, with every factor transporter discharged.
The decomposition is universally quantified in the conclusion, so its complete
E.6.7 action and Borel clauses are available for each actual factor. No block
persistence, containing block, or factor identification is assumed. -/
theorem envelopeCentralizerProduct
    {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 K T M V) (h21 : OddCoreFree V) :
    EnvelopeCentralizerProduct T M V := by
  apply envelopeCentralizerProduct_of_factorTransporters h
  intro U hU hUh A hA hAU hc d i hi
  rcases d.type i with ⟨n, hL⟩ | hL | hL
  · exact envelope_factor_natural_transporter h h21 hU hUh hA hAU hc d i hL hi
  · exact alternating_factor_transporter h h21 hA d i 3 hL hU.1 hi
  · exact alternating_factor_transporter h h21 hA d i 5 hL hU.1 hi

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
