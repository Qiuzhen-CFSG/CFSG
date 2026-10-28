module

public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.SylowCore
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeCenters
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeDerived
public import Stellmacher.Recognition.Parrott.LocalNormalizer.InvolutionCosets
public import Stellmacher.Recognition.Parrott.NormalizerCompatibleGenerators
public import Stellmacher.Recognition.Parrott.NormalizerCosetReflection
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransport
public import Stellmacher.Recognition.Parrott.NormalizerSquareRootSelection
public import Stellmacher.Recognition.Parrott.SecondNormalizerGrowthLocal

/-!
# Parrott generators from local inputs: Normalizer

An odd cyclic reflection interchanges the yF and wF cosets. The proved
involution-orbit census selects its exact y-image; square-root normalization
then yields the two possible x-images. The compatible change x ↦ xz,
s ↦ svt interchanges these branches and supplies (25)–(26), including actual
normalizer generation and the involution's order and conjugacy class.

The derived-core normalizer identity and local normalizer solvability in
`ParrottLocalInputs` replace the ambient N₂ assumption. The original APIs
remain unchanged, and F, the supplied Sylow subgroup, t and v remain literal.

Source: D. Parrott, *A characterization of the Tits simple group* (1972),
§3, printed pp.678–682, with the local geometry of §§1–2.
-/

section

/- NormalizerCosetReflection: local-input version of the original construction. -/

open Subgroup
open scoped IsMulCommutative Pointwise
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
private theorem NormalizerCosetReflection_d_not_core (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    f.d ∉ (pCore 2 (normalizer (e.F : Set G))).map (normalizer (e.F : Set G)).subtype := by
  intro hd
  rw [n.core_eq_sylow_centralizer] at hd
  have hc : Commute f.d n.t := mem_centralizer_singleton_iff.mp hd.2
  have hz1 : z = 1 := f.eq03_dt.symm.trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
  have hz := h.involution
  rw [hz1, orderOf_one] at hz
  norm_num at hz
private theorem NormalizerCosetReflection_w_not_elementary (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z) :
    f.w ∉ e.F := by
  intro hw
  let _ := e.elementary
  have ha : f.a ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hc : Commute f.a f.w := congrArg e.F.subtype
    (mul_comm (⟨f.a, ha⟩ : e.F) ⟨f.w, hw⟩)
  have hz1 : z = 1 := f.eq02_aw.symm.trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr hc)
  have hz := h.involution
  rw [hz1, orderOf_one] at hz
  norm_num at hz
private theorem NormalizerCosetReflection_y_not_join (f : ParrottSylowGeneratorData n) :
    f.y ∉ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) ⊔ e.F := by
  let C := centralizer ({f.u} : Set G)
  have hEC : (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) ≤ C := by
    rw [← f.derived_basis]
    apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr f.comm_zu.eq
    · exact mem_centralizer_singleton_iff.mpr f.comm_tu.eq
    · exact mem_centralizer_singleton_iff.mpr f.comm_vu.eq
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact mem_centralizer_singleton_iff.mpr f.comm_uw.symm.eq
  have huF : f.u ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hFC : e.F ≤ C := by
    let _ := e.elementary
    intro g hg
    exact mem_centralizer_singleton_iff.mpr
      (congrArg e.F.subtype (mul_comm (⟨g, hg⟩ : e.F) ⟨f.u, huF⟩))
  intro hy
  have hc : Commute f.y f.u := mem_centralizer_singleton_iff.mp ((sup_le hEC hFC) hy)
  have he : (MulAut.conj f.y⁻¹) f.u = f.u := by
    change f.y⁻¹ * f.u * f.y⁻¹⁻¹ = f.u
    rw [hc.inv_left.eq, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have ht1 : n.t = 1 := by
    have ht := f.y_conjugation.2.1
    rw [he] at ht
    exact (mul_eq_left.mp ht.symm)
  have ht := n.t_order
  rw [ht1, orderOf_one] at ht
  norm_num at ht
private theorem NormalizerCosetReflection_y_mem_core (f : ParrottSylowGeneratorData n) :
    f.y ∈ (pCore 2 (normalizer (e.F : Set G))).map (normalizer (e.F : Set G)).subtype := by
  let X := (pCore 2 (normalizer (e.F : Set G))).map (normalizer (e.F : Set G)).subtype
  have hzX : z ∈ X := n.omega_le_core (n.elementary_le_omega e.z_mem_inf.2)
  have hyz : f.y * z ∈ X := f.eq04 ▸ X.pow_mem f.x_mem_normalizer_core 2
  exact (X.mul_mem_cancel_right hzX).mp hyz
private theorem NormalizerCosetReflection_join_coset [Finite G] (f : ParrottSylowGeneratorData n)
    (h : ParrottCentralizerHypotheses z) (g : G)
    (hg : g ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) ⊔ e.F)
    (hgF : g ∉ e.F) : f.w⁻¹ * g ∈ e.F := by
  classical
  let E := (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)
  have huF : f.u ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hwE : f.w ∈ E := by
    dsimp only [E]
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  have hgen : E ⊔ e.F = zpowers f.w ⊔ e.F := by
    apply le_antisymm
    · apply sup_le ?_ le_sup_right
      change (commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype) ≤ _
      rw [← f.derived_basis]
      apply (closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact mem_sup_right e.z_mem_inf.2
      · exact mem_sup_right n.t_mem_inf.2
      · exact mem_sup_right n.v_mem_inf.2
      · exact mem_sup_right huF
      · exact mem_sup_left (mem_zpowers f.w)
    · exact sup_le (zpowers_le.mpr (mem_sup_left hwE)) le_sup_right
  have hwN : f.w ∈ normalizer (e.F : Set G) :=
    e.sylow_le_normalizer f.local_mem_sylow.2.2.2.2.1
  have hprod : g ∈ (zpowers f.w : Set G) * (e.F : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (zpowers_le.mpr hwN), ← hgen]
    exact hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod
  have hw1 : f.w ≠ 1 := fun hh => NormalizerCosetReflection_w_not_elementary f h (hh.symm ▸ e.F.one_mem)
  have hwo : orderOf f.w = 2 := orderOf_eq_prime f.w_sq hw1
  change a ∈ zpowers f.w at ha
  change b ∈ e.F at hb
  rw [mem_zpowers_iff_mem_range_orderOf, hwo] at ha
  have ha' : a = 1 ∨ a = f.w := by
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    have hi' : i < 2 := Finset.mem_range.mp hi
    have hi'' : i = 0 ∨ i = 1 := by omega
    rcases hi'' with rfl | rfl
    · exact Or.inl (by simpa using hia.symm)
    · exact Or.inr (by simpa using hia.symm)
  rcases ha' with rfl | rfl
  · exact False.elim (hgF (by simpa using hb))
  · simpa only [inv_mul_cancel_left] using hb
private theorem NormalizerCosetReflection_join_normalized_by_sylow :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    (e.sylow : Subgroup G) ≤ normalizer ((E ⊔ e.F : Subgroup G) : Set G) := by
  intro H J E
  let DH := (commutator J).map J.subtype
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := le_normalizer_map (H := DH) H.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, DH, E, map_map] using hh
  exact (le_inf (e.sylow_le_centralizer.trans hHE) e.sylow_le_normalizer).trans
    (normalizer_inf_normalizer_le_normalizer_sup E e.F)

/-- A conjugate of the supplied d interchanges yF and wF. This construction
already works for the supplied Sylow frame, without its centralizer extension. -/
public theorem ParrottSylowGeneratorData.exists_normalizer_coset_reflection_of_local_inputs
    [Finite G] (f : ParrottSylowGeneratorData n)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    ∃ s : G, s ∈ normalizer (e.F : Set G) ∧ s ∉ (e.sylow : Subgroup G) ∧
      s ^ 2 = 1 ∧ f.w⁻¹ * (s⁻¹ * f.y * s) ∈ e.F := by
  classical
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let F₀ := e.F.subgroupOf N
  let : F₀.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  let π := QuotientGroup.mk' F₀
  let _ : MulAction N (N ⧸ F₀) :=
    MulAction.compHom (N ⧸ F₀) (MulAut.conj.comp π)
  let _ : SMul N (N ⧸ F₀) := (inferInstance : MulAction N (N ⧸ F₀)).toSMul
  have action_eq (a b : N) : a • π b = π (a * b * a⁻¹) := by
    change π a * π b * (π a)⁻¹ = π (a * b * a⁻¹)
    simp only [map_mul, map_inv]
  obtain ⟨_, _, _, _, hwT, _, _, _, hdT, _, hyT⟩ := f.local_mem_sylow
  let dN : N := ⟨f.d, e.sylow_le_normalizer hdT⟩
  let wN : N := ⟨f.w, e.sylow_le_normalizer hwT⟩
  let yN : N := ⟨f.y, e.sylow_le_normalizer hyT⟩
  have hdK : dN ∉ K := fun hd => NormalizerCosetReflection_d_not_core f h (mem_map_of_mem N.subtype hd)
  have hd2 : dN ^ 2 = 1 := Subtype.ext f.d_sq
  have hdo : orderOf dN = 2 := orderOf_eq_prime hd2
    (fun hd => hdK (hd.symm ▸ K.one_mem))
  obtain ⟨R, hR, hinv⟩ := exists_inverted_three_of_symmetric_three_quotient
    K pCore_isPGroup n.core_quotient dN hdo hdK
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic R := isCyclic_of_prime_card hR
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by simpa using hR)
  obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
  have hRQeq : R = (Q : Subgroup N) := eq_of_le_of_card_ge hRQ (by
    rw [hR, e.normalizer_three_card_of_local_inputs h hlocal n.sylow_lt_normalizer Q])
  have hyF : f.y ∉ e.F := fun hy => NormalizerCosetReflection_y_not_join f (mem_sup_right hy)
  obtain ⟨q, hq⟩ := e.normalizer_core_involution_transport_of_local_inputs h hlocal
    n.sylow_lt_normalizer Q
    (e.normalizer_three_centralizer_le_derived_of_local_inputs h hlocal n.sylow_lt_normalizer Q)
    f.y (NormalizerCosetReflection_y_mem_core f) f.y_sq
  have hqF : ((q : N) : G) * f.y * ((q : N) : G)⁻¹ ∉ e.F :=
    fun hh => hyF ((mem_normalizer_iff.mp (q : N).property f.y).mpr hh)
  have hdiff := NormalizerCosetReflection_join_coset f h _ hq hqF
  let qR : R := ⟨q, hRQeq.symm ▸ q.property⟩
  have hqw : (qR : N) • π yN = π wN := by
    rw [action_eq]
    exact (QuotientGroup.eq.mpr (show wN⁻¹ * ((qR : N) * yN * (qR : N)⁻¹) ∈ F₀ from hdiff)).symm
  have hyrot : π yN = ((qR⁻¹ : R) : N) • π wN := by
    rw [← hqw]
    exact (inv_smul_smul (qR : N) (π yN)).symm
  have hdw : dN • π wN = π wN := by
    rw [action_eq]
    congr 1
    apply Subtype.ext
    change f.d * f.w * f.d⁻¹ = f.w
    have hc := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq07_dw
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨c, hswap, _⟩ := exists_conjugate_reflection_swapping R hRp
    (by decide : Odd 3) dN (π wN) hdw (fun r => hinv r r.property) qR⁻¹ 1
  let sN : N := (c : N) * dN * (c : N)⁻¹
  have hs2 : sN ^ 2 = 1 := by
    change ((c : N) * dN * (c : N)⁻¹) ^ 2 = 1
    calc
      _ = (c : N) * dN ^ 2 * (c : N)⁻¹ := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hd2]; simp
  have hsi : sN⁻¹ = sN := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs2)
  have hsy : sN • π yN = π wN := by
    rw [hyrot]
    simpa only [Subgroup.coe_one, one_smul] using hswap
  have hmem : f.w⁻¹ * ((sN : G)⁻¹ * f.y * (sN : G)) ∈ e.F := by
    have heq : π (sN⁻¹ * yN * sN) = π wN := by
      rw [hsi]
      have heq : sN * yN * sN = sN * yN * sN⁻¹ := by rw [hsi]
      rw [heq]
      exact (action_eq sN yN).symm.trans hsy
    exact (QuotientGroup.eq.mp heq.symm : wN⁻¹ * (sN⁻¹ * yN * sN) ∈ F₀)
  refine ⟨sN, sN.property, ?_, congrArg N.subtype hs2, hmem⟩
  intro hsT
  let E := (commutator (pCore 2 (centralizer ({z} : Set G)))).map
    ((centralizer ({z} : Set G)).subtype.comp
      (pCore 2 (centralizer ({z} : Set G))).subtype)
  have hwE : f.w ∈ E := by
    dsimp only [E]
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  have hA : (sN : G)⁻¹ * f.y * (sN : G) ∈ E ⊔ e.F := by
    have hh := (E ⊔ e.F).mul_mem (mem_sup_left hwE) (mem_sup_right hmem)
    simpa only [mul_inv_cancel_left] using hh
  exact NormalizerCosetReflection_y_not_join f ((mem_normalizer_iff''.mp
    (NormalizerCosetReflection_join_normalized_by_sylow hsT) f.y).mpr hA)

/-- The initial coset-moving involution for the literal supplied centralizer
frame, under the centralizer hypotheses and local inputs. -/
public theorem ParrottCentralizerGeneratorData.exists_normalizer_coset_reflection_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (_hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ s₀ : G, s₀ ∈ normalizer (e.F : Set G) ∧ s₀ ∉ (e.sylow : Subgroup G) ∧
      s₀ ^ 2 = 1 ∧ f.w⁻¹ * (s₀⁻¹ * f.y * s₀) ∈ e.F :=
  f.toParrottSylowGeneratorData.exists_normalizer_coset_reflection_of_local_inputs h hlocal

end Stellmacher.Recognition

end

section

/- NormalizerInvolutionTransport: local-input version of the original construction. -/

open Subgroup

namespace Stellmacher.Recognition.ParrottCentralizerGeneratorData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Construct the normalizer transport involution on the literal supplied frame.
The coset reflection and its eight-element involution orbit select the image
of y; the commutator deductions supply the required images of t and v. -/
public theorem exists_normalizer_transport_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottNormalizerTransportData f) :=
  f.exists_normalizer_transport_of_coset_movement
    (f.exists_normalizer_coset_reflection_of_local_inputs hns hlocal h)
    (f.exists_normalizer_involution_y_image h)

end Stellmacher.Recognition.ParrottCentralizerGeneratorData

end

section

/- NormalizerSquareRootSelection: local-input version of the original construction. -/

namespace Stellmacher.Recognition.ParrottCentralizerGeneratorData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The proved involution transport leaves only square-root normalization.
The normalization may replace the transport involution, but must retain the
literal supplied elementary subgroup, fusion witnesses and centralizer frame. -/
public theorem exists_normalizerSeed_of_normalization_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z)
    (hnormalize : ParrottNormalizerTransportData f → Nonempty (ParrottNormalizerSeedData f)) :
    Nonempty (ParrottNormalizerSeedData f) :=
  f.exists_normalizerSeed_of_transport_normalization
    (f.exists_normalizer_transport_of_local_inputs hns hlocal h) hnormalize

/-- The root-fiber census supplies the normalization for the transported
involution, completing the unconditional seed construction. -/
public theorem exists_normalizerSeed_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottNormalizerSeedData f) :=
  f.exists_normalizerSeed_of_normalization_of_local_inputs hns hlocal h
    (fun k => k.exists_seed h)

end Stellmacher.Recognition.ParrottCentralizerGeneratorData

end

section

/- NormalizerCompatibleGenerators: local-input version of the original construction. -/

open Subgroup Tits
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Construct compatible centralizer and normalizer frames on the supplied
actual elementary and Sylow subgroups. Only the auxiliary x may be changed. -/
public theorem ParrottCentralizerGeneratorData.exists_normalized_normalizer_generators_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    ∃ f' : ParrottCentralizerGeneratorData n,
      (f'.u, f'.w, f'.a, f'.b, f'.c, f'.d, f'.y, f'.r) =
        (f.u, f.w, f.a, f.b, f.c, f.d, f.y, f.r) ∧
      (f'.x = f.x ∨ f'.x = f.x*z) ∧
      Nonempty (ParrottNormalizerGeneratorData f') := by
  obtain ⟨k⟩ := f.exists_normalizerSeed_of_local_inputs hns hlocal h
  obtain ⟨f', k', hcoords, hchoice, hxs⟩ := k.exists_normalized_frame
  obtain ⟨hws, has, hbs, hcs, hxs, hcube⟩ := k'.equations_of_x_conj hxs
  refine ⟨f', hcoords, hchoice, ?_⟩
  exact ⟨f'.normalizerGeneratorDataOfEquations h k'.s k'.mem_normalizer k'.sq
    k'.t_conj k'.v_conj k'.y_conj hws has hbs hcs hxs hcube⟩

/-- The existential compatible generator packet needed by the actual local
presentation, retaining the original F,T,t,v through the parameter n. -/
public theorem ParrottCentralizerGeneratorData.nonempty_compatible_generator_data_of_local_inputs
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hlocal : ParrottLocalInputs z)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (Σ f' : ParrottCentralizerGeneratorData n, ParrottNormalizerGeneratorData f') := by
  obtain ⟨f', _, _, ⟨k⟩⟩ := f.exists_normalized_normalizer_generators_of_local_inputs hns hlocal h
  exact ⟨⟨f', k⟩⟩

end Stellmacher.Recognition

end
