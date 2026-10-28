module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.SecondFactorResidual
public import Theory.GroupAction.BinaryWreathPointStabilizer

/-!
# The full second parabolic in the original orthogonal branch

For the faithful action on [U_H,H]/Z, compatibility identifies the intrinsic
kernel C_H(u mod Z) with the full matrix point stabilizer. Its second-plane
projection is onto GL₂(2), with two-group kernel. The original second factor,
when identified by the earlier-source marking, has relative index two in this
full parabolic, so its embedded two-residual agrees with that of the parabolic.
The full orthogonal actor also gives the exact original Sylow/core index eight.

The source applications keep the original H, M, Mc and u. The terminal
application discharges its parabolic-action and core-index inputs; residual
coordinates, crossing geometry and the module-rank bound remain explicit here.
This module does not assert completion of 14.6.17 or construction of those inputs.

Source: Aschbacher--Smith, 14.6.12--17, printed pp.1031--1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G]
namespace SourceOrthogonalFourAction
variable {H U Z Q : Subgroup G} (d : SourceOrthogonalFourAction H U Z Q)
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

/-- The actual quotient coordinate fixes a vector exactly modulo the source line. -/
theorem fixed_iff_commutator_mem (x : H) (u : (⁅U,H⁆ : Subgroup G)) :
    d.actor x • d.coordinates u = d.coordinates u ↔ ⁅(u : G),(x : G)⁆ ∈ Z := by
  let y := ⁅U,H⁆.normalizerMonoidHom
    ⟨x,normalizer_commutator_ge_right U H x.property⟩ u
  let w : (⁅U,H⁆ : Subgroup G) := u * y⁻¹
  have hw : (w : G) = ⁅(u : G),(x : G)⁆ := by
    change (u : G) * ((x : G) * (u : G) * (x : G)⁻¹)⁻¹ = _
    rw [commutatorElement_def]
    group
  have hk : d.coordinates w = 1 ↔ (w : G) ∈ Z := by
    change w ∈ d.coordinates.ker ↔ _
    rw [d.vector_kernel]
    rfl
  have hy : d.coordinates y = d.actor x • d.coordinates u := d.compatible x u
  rw [show d.coordinates w = d.coordinates u * (d.actor x • d.coordinates u)⁻¹ by
    simp only [w,map_mul,map_inv,hy],mul_inv_eq_one,hw] at hk
  exact eq_comm.trans hk

/-- Membership of a lift in the covering plane is its literal coordinate support. -/
theorem mem_plane_iff (i : OrthogonalPlaneIndex) (u : (⁅U,H⁆ : Subgroup G)) :
    (u : G) ∈ d.plane i ↔
      BinaryWreathPointStabilizer.Supported i (d.coordinates u) := by
  constructor
  · rintro ⟨v,hv,he⟩
    have he' : v = u := Subtype.ext he
    exact he' ▸ hv
  · intro hu
    exact ⟨u,hu,rfl⟩

/-- The literal factor above the second direct factor of the faithful actor. -/
def secondFactor (i : OrthogonalPlaneIndex) : Subgroup G :=
  ((BinaryWreathPointStabilizer.secondFactor i).comap d.actor).map H.subtype

end SourceOrthogonalFourAction

namespace OddCriticalPair
variable [Finite G] {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

omit [Finite G] in
private theorem cyclic_square_one_cases (u : G) (hu2 : u ^ 2 = 1)
    (a : G) (ha : a ∈ zpowers u) : a = 1 ∨ a = u := by
  let A : Subgroup G := {
    carrier := {a | a = 1 ∨ a = u}
    one_mem' := Or.inl rfl
    mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> simp_all [pow_two]
    inv_mem' := by
      rintro a (rfl | rfl)
      · simp
      · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu2)) }
  exact (zpowers_le.mpr (show u ∈ A from Or.inr rfl)) ha

/-- The full intrinsic parabolic is the preimage of the marked point stabilizer. -/
theorem suitable_kernel_eq_point_preimage
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu2 : (u : G)^2 = 1) :
    h.kernel (zpowers (u : G)) =
      ((MulAction.stabilizer OrthogonalActor (d.coordinates u)).comap d.actor).map D.H.subtype := by
  have huH : (u : G) ∈ D.H :=
    ((Subgroup.commutator_le_sup D.UH D.H).trans (sup_le h.UH_le_H le_rfl)) u.property
  ext x
  rw [h.mem_kernel_iff (zpowers_le.mpr huH)]
  constructor
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    exact (d.fixed_iff_commutator_mem ⟨x,hx⟩ u).mpr (hc u (mem_zpowers _))
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,fun a ha => ?_⟩
    rcases cyclic_square_one_cases (u : G) hu2 a ha with rfl | rfl
    · simp
    · exact (d.fixed_iff_commutator_mem x u).mp hx

/-- A full second-plane action on P itself, with explicit matrix compatibility. -/
theorem suitable_binary_plane_action
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu2 : (u : G)^2 = 1)
    (hu : (u : G) ∈ d.plane i) (huz : (u : G) ∉ D.V₁) :
    ∃ a : SourceBinaryPlaneAction (h.kernel (zpowers (u : G))),
      ∀ x : h.kernel (zpowers (u : G)), ∀ hx : (x : G) ∈ D.H,
        a.actor x = BinaryLinear.OuterCyclic.slEquivLinear 2 ((d.actor ⟨x,hx⟩).left j) := by
  let P := h.kernel (zpowers (u : G))
  let B := MulAction.stabilizer OrthogonalActor (d.coordinates u)
  have huH : (u : G) ∈ D.H :=
    ((Subgroup.commutator_le_sup D.UH D.H).trans (sup_le h.UH_le_H le_rfl)) u.property
  have hPH : P ≤ D.H := fun x hx => ((h.mem_kernel_iff (zpowers_le.mpr huH)).mp hx).1
  let inc : P →* D.H := inclusion hPH
  let f : P →* B := (d.actor.comp inc).codRestrict B (fun x => by
    apply (d.fixed_iff_commutator_mem (inc x) u).mpr
    exact ((h.mem_kernel_iff (zpowers_le.mpr huH)).mp x.property).2 u (mem_zpowers _))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := d.onto y
    have hxP : (x : G) ∈ P := by
      change (x : G) ∈ h.kernel (zpowers (u : G))
      rw [suitable_kernel_eq_point_preimage h d u hu2]
      exact ⟨x,show d.actor x ∈ B from hx ▸ y.property,rfl⟩
    exact ⟨⟨x,hxP⟩,Subtype.ext hx⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = d.actor.ker.comap inc := by ext x; exact Subtype.ext_iff
    rw [he,d.actor_kernel]
    exact (isPGroup_pCoreIn 2 D.H).comap_subtype.comap_of_injective inc (inclusion_injective hPH)
  have hs := (d.mem_plane_iff i u).mp hu
  have hn : d.coordinates u ≠ 1 := by
    intro he
    have huK : u ∈ d.coordinates.ker := he
    rw [d.vector_kernel] at huK
    exact huz huK
  let s := BinaryWreathPointStabilizer.secondActor hs hn j
  let e := BinaryLinear.OuterCyclic.slEquivLinear 2
  let actor := e.toMonoidHom.comp (s.comp f)
  have hactor : Function.Surjective actor :=
    e.surjective.comp ((BinaryWreathPointStabilizer.secondActor_surjective hs hn hji).comp hf)
  have hker : IsPGroup 2 actor.ker := by
    have he : actor.ker = s.ker.comap f := by
      ext x
      change e (s (f x)) = 1 ↔ s (f x) = 1
      exact e.map_eq_one_iff
    rw [he]
    exact (BinaryWreathPointStabilizer.secondActor_kernel hs hn hji).comap_of_ker_isPGroup f hk
  exact ⟨⟨actor,hactor,hker⟩,fun _ _ => rfl⟩

/-- The original second factor lies in the full point stabilizer with index two. -/
theorem second_factor_index
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i : OrthogonalPlaneIndex)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu2 : (u : G)^2 = 1)
    (hu : (u : G) ∈ d.plane i) (huz : (u : G) ∉ D.V₁) :
    d.secondFactor i ≤ h.kernel (zpowers (u : G)) ∧
      (d.secondFactor i).relIndex (h.kernel (zpowers (u : G))) = 2 := by
  have hs := (d.mem_plane_iff i u).mp hu
  have hn : d.coordinates u ≠ 1 := by
    intro he
    have huK : u ∈ d.coordinates.ker := he
    rw [d.vector_kernel] at huK
    exact huz huK
  rw [suitable_kernel_eq_point_preimage h d u hu2]
  constructor
  · exact map_mono (comap_mono (BinaryWreathPointStabilizer.secondFactor_le_stabilizer hs))
  · change (((BinaryWreathPointStabilizer.secondFactor i).comap d.actor).map D.H.subtype).relIndex
      (((MulAction.stabilizer OrthogonalActor (d.coordinates u)).comap d.actor).map D.H.subtype) = 2
    rw [relIndex_map_map_of_injective _ _ D.H.subtype_injective,relIndex_comap,
      map_comap_eq,MonoidHom.range_eq_top.mpr d.onto,top_inf_eq]
    exact BinaryWreathPointStabilizer.secondFactor_relIndex hs hn

/-- The original H₂ and full P have the same two-residual embedded in G. -/
theorem second_factor_residual
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i : OrthogonalPlaneIndex) (H2 : Subgroup G) (hH2 : H2 = d.secondFactor i)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu2 : (u : G)^2 = 1)
    (hu : (u : G) ∈ d.plane i) (huz : (u : G) ∉ D.V₁) :
    H2 ≤ h.kernel (zpowers (u : G)) ∧ H2.relIndex (h.kernel (zpowers (u : G))) = 2 ∧
      (pResidual 2 H2).map H2.subtype =
        (pResidual 2 (h.kernel (zpowers (u : G)))).map (h.kernel (zpowers (u : G))).subtype := by
  obtain ⟨hP,hi⟩ := second_factor_index h d i u hu2 hu huz
  rw [← hH2] at hP hi
  refine ⟨hP,hi,?_⟩
  have huU : (u : G) ∈ D.UH :=
    (le_normalizer_iff_commutator_le_left.mp d.normalized) u.property
  have huH := h.UH_le_H huU
  have h2H : H2 ≤ D.H := hH2 ▸ map_subtype_le _
  apply second_factor_residual_eq_suitable_kernel h u huU H2 h2H _ hi
  apply commutator_le.mpr
  intro a ha x hx
  exact ((h.mem_kernel_iff (zpowers_le.mpr huH)).mp (hP hx)).2 a ha

include h in
/-- The full faithful orthogonal actor makes the original core's Sylow index eight. -/
theorem orthogonal_core_index
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH) :
    D.QH.relIndex (D.T : Subgroup G) = 8 := by
  have hTH : (D.T : Subgroup G) ≤ D.H := le_sup_right.trans h.local_le
  let P : Sylow 2 OrthogonalActor := (D.T.subtype hTH).mapSurjective d.onto
  rw [← relIndex_subgroupOf hTH,← d.actor_kernel,relIndex_ker]
  change Nat.card P = 8
  rw [P.card_eq_multiplicity]
  have hcard : Nat.card OrthogonalActor = 72 := by
    rw [RegularWreathProduct.card]
    have hs : Nat.card OrthogonalPlaneActor = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hs]
    norm_num [OrthogonalPlaneIndex,Nat.card_eq_fintype_card]
  rw [hcard]
  decide +kernel

end OddCriticalPair

open SourcePreliminaries ChapterA.Section05To06
variable [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

/-- Original 14.6.17's parabolic and residual calculation on the same chosen u.
The earlier orthogonal marking identifies the literal H₂ with its matrix factor;
the full point stabilizer, its quotient and its residual are conclusions. -/
theorem source_orthogonal_parabolic_and_residual
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i)
    (H2 : Subgroup G) (hH2 : H2 = d.secondFactor i)
    (u : G) (hu : u ∈ d.plane i) (huz : u ∉ centralInvolutions T) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let P := h.kernel (zpowers u)
    Nonempty (SourceParabolicAction P) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      H2 ≤ P ∧ H2.relIndex P = 2 ∧
      (pResidual 2 H2).map H2.subtype = (pResidual 2 P).map P.subtype ∧
      4 < (H.pCoreIn 2).relIndex (T : Subgroup G) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have huK := d.plane_le i hu
  have huU : u ∈ conjugateSpanBy (localModule T M) H :=
    (le_normalizer_iff_commutator_le_left.mp d.normalized) huK
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian
    (A := conjugateSpanBy (localModule T M) H) u huU
  obtain ⟨a,_⟩ := OddCriticalPair.suitable_binary_plane_action h d i j hji ⟨u,huK⟩ hu2 hu huz
  obtain ⟨hP,hi,hr⟩ := OddCriticalPair.second_factor_residual h d i H2 hH2 ⟨u,huK⟩ hu2 hu huz
  have hc := OddCriticalPair.orthogonal_core_index h d
  exact ⟨⟨.plane a⟩,(SourceParabolicAction.plane a).quotient,hP,hi,hr,by
    change (H.pCoreIn 2).relIndex (T : Subgroup G) = 8 at hc
    omega⟩

/-- Apply the constructed orthogonal parabolic at the literal terminal surface.
The residual coordinates, crossing, and module-rank bound remain explicit here;
their construction is retained by the terminal-geometry assembly owner. -/
theorem source_terminal_witness_of_orthogonal_parabolic
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i)
    (u : G) (hu : u ∈ d.plane i) (huz : u ∉ centralInvolutions T)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (c : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
        H hH).kernel (zpowers u))).map
        ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
          H hH).kernel (zpowers u)).subtype))
    (f : SourceCrossingGeometry (localModule T M) H Mc u) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  obtain ⟨⟨a⟩,_,_,_,_,hcore⟩ := source_orthogonal_parabolic_and_residual
    hG T hempty hM hunique hmany hcard e hab H hH d i j hji
      (d.secondFactor i) rfl u hu huz
  have huU : u ∈ conjugateSpanBy (localModule T M) H :=
    (le_normalizer_iff_commutator_le_left.mp d.normalized) (d.plane_le i hu)
  exact source_terminal_witness_of_geometry hG T hempty hM hunique hmany hcard e hab H hH
    u huU hindex hmove hproduct hU3 hcore hrank a c f

end CFSG.Quasithin.Chapter14.Section06
