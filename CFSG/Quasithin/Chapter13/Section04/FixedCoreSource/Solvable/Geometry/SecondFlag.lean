module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.PlaneMarking
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ChiefFactors

/-!
# Chief factors and fixed points of the original second parabolic

Let V₂ be the preimage of the original T-invariant plane, B=N_LT(V₂),
and L₂=O²(B), mapped into G by B's inclusion. The constructed flag
alignment gives B/O₂(B)≅S₃, three noncentral binary chief factors of L₂,
and C_V(L₂)=C_V(L). The inner syntheme stabilizer is maximal in A₆;
the quotient map and the original T supplement lift maximality to B in LT.

OriginalPlane applies these results to the original-R₁ amalgam, removing
its supplied parabolic marking, maximality and residual fixed-line
premises. The fixed space is computed on the five-dimensional V before
restricting to the full omega-center, so no equality between these spaces
is presumed. Source: Aschbacher–Smith Notation 13.2.1 and 13.4.9,
printed pp.877 and906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal source plane normalizer is the inner normalizer times T. -/
theorem second_flag_normalizer_eq
    (D : ChosenModule T L V) (U : Subgroup G)
    (hT : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    (L ⊔ (T : Subgroup G)) ⊓ normalizer (U : Set G) =
      (L ⊓ normalizer (U : Set G)) ⊔ (T : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G) D.sylow_normalizes_component]
      exact hx.1
    obtain ⟨l,hl,t,ht,rfl⟩ := hp
    have hln : l ∈ normalizer (U : Set G) := by
      have hh := (normalizer (U : Set G)).mul_mem hx.2 ((normalizer (U : Set G)).inv_mem (hT ht))
      simpa only [mul_inv_cancel_right] using hh
    exact ((L ⊓ normalizer (U : Set G)) ⊔ (T : Subgroup G)).mul_mem (mem_sup_left ⟨hl,hln⟩) (mem_sup_right ht)
  · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hT)

variable [Finite G]
/-- The actual T-invariant plane of Notation 13.2.1 supplies its own parabolic
marking, S₃ quotient and three noncentral binary chief factors. -/
theorem original_second_flag_chief_factors
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let K := (pResidual 2 B).map B.subtype
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      K ≤ L ∧ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      (∀ s : NoncentralChiefRefinement.ChiefSeries K,
        s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) := by
  let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
  have hJL : J ≤ L := inf_le_left
  have hTJ := m.sylow_normalizes_inner_plane W hT
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hT
  have himage := m.aligned_inner_plane_image W g hg
  have hres := second_parabolic_full_residual J hTJ
  dsimp only
  rw [second_flag_normalizer_eq D _ hT]
  change Nonempty (((J ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧ _
  rw [hres]
  exact ⟨second_parabolic_full_core_quotient D (m.relabel g) eL J hJL hTJ himage,
    (map_subtype_le _).trans hJL,
    hTJ.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J)),
    second_parabolic_residual_three_chief_factors D (m.relabel g) eL J hJL hTJ himage⟩

/-- In the original core the plane residual fixes exactly the component's
constant line; the residual has the literal quotient map of the marking. -/
theorem marked_second_residual_fixed
    (D : ChosenModule T L V) (m : CoreMarking D)
    (J : Subgroup G) (hJL : J ≤ L)
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6)) :
    V ⊓ centralizer (((pResidual 2 J).map J.subtype : Subgroup G) : Set G) =
      V ⊓ centralizer (L : Set G) := by
  let K := (pResidual 2 J).map J.subtype
  have hKL : K ≤ L := (map_subtype_le _).trans hJL
  obtain ⟨f,hf,hmark⟩ := second_parabolic_residual_action D m J hJL himage
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := ResidualPairRecognition.A) 3
    (by rw [nat_card_alternatingGroup]; norm_num)
  obtain ⟨k,hk⟩ := hf a
  apply le_antisymm ?_ (inf_le_inf_left V (centralizer_le hKL))
  intro v hv
  refine ⟨hv.1,(m.mem_fixed_iff ⟨v,hv.1⟩).mpr ?_⟩
  apply (SynthemeCoreChief.cubic_fixed_iff (f k) (hk ▸ ha) _).mp
  rw [←hmark k,←m.equivariant (inclusion hKL k)]
  congr 2
  apply Subtype.ext
  change k.val * v * k.val⁻¹ = v
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 k.val k.property)

theorem original_second_flag_fixed
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let K := (pResidual 2 B).map B.subtype
    V ⊓ centralizer (K : Set G) = V ⊓ centralizer (L : Set G) := by
  let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTJ := m.sylow_normalizes_inner_plane W hT
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hT
  have himage := m.aligned_inner_plane_image W g hg
  dsimp only
  rw [second_flag_normalizer_eq D _ hT,second_parabolic_full_residual J hTJ]
  exact marked_second_residual_fixed D (m.relabel g) J inf_le_left himage

theorem original_inner_plane_coatom
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    IsCoatom ((L ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf L) := by
  let J := (L ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf L
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hT
  let q : L →* alternatingGroup (Fin 6) :=
    (m.relabel g).quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hq : Function.Surjective q :=
    (m.relabel g).quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have himage : J.map q = a6SynthemeStabilizer := by
    apply map_injective (alternatingGroup (Fin 6)).subtype_injective
    rw [map_map]
    rw [m.aligned_inner_plane_image W g hg]
    ext a
    constructor
    · rintro ⟨hs,ha⟩
      exact ⟨⟨a,ha⟩,hs,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨ha,a.property⟩
  have hk : q.ker ≤ J := by
    intro l hl
    refine ⟨l.property,(m.normalizes_naturalPreimage_iff W l).mpr ?_⟩
    change (MulAut.conj g⁻¹) (m.quotient (QuotientGroup.mk' (centralCore L) l)) = 1 at hl
    rw [(MulAut.conj g⁻¹).map_eq_one_iff] at hl
    rw [hl]
    exact one_mem _
  have he : J = a6SynthemeStabilizer.comap q := by
    rw [←himage,comap_map_eq_self hk]
  change IsCoatom J
  rw [he]
  exact isCoatom_comap_of_surjective hq a6SynthemeStabilizer_isCoatom

theorem original_second_flag_coatom
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    IsCoatom (((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G))) := by
  let X := L ⊔ (T : Subgroup G)
  let U := m.naturalPreimage W
  let B := X ⊓ normalizer (U : Set G)
  let J := L ⊓ normalizer (U : Set G)
  have hLX : L ≤ X := le_sup_left
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hmax : IsCoatom (J.subgroupOf L) := original_inner_plane_coatom D m W hW hT
  have hnot : ¬ L ≤ B := by
    intro hLB
    apply hmax.1
    apply top_unique
    intro l _
    exact ⟨l.property,(hLB l.property).2⟩
  refine ⟨?_,?_⟩
  · intro he
    apply hnot
    intro l hl
    have hh : (⟨l,hLX hl⟩ : X) ∈ B.subgroupOf X := he ▸ mem_top _
    exact hh
  · intro C hC
    let Y := C.map X.subtype
    have hYX : Y ≤ X := map_subtype_le _
    have hBY : B ≤ Y := by
      have hh : (B.subgroupOf X).map X.subtype ≤ Y := map_mono hC.le
      rwa [map_subgroupOf_eq_of_le (show B ≤ X from inf_le_left)] at hh
    have hTY : (T : Subgroup G) ≤ Y := hTB.trans hBY
    have hJY : J.subgroupOf L ≤ Y.subgroupOf L := by
      intro l hl
      exact hBY ⟨hLX hl.1,hl.2⟩
    have hLY : L ≤ Y := by
      by_cases he : J.subgroupOf L = Y.subgroupOf L
      · have hYB : Y ≤ B := by
          intro x hx
          have hp : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
            rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G) D.sylow_normalizes_component]
            exact hYX hx
          obtain ⟨l,hl,t,ht,rfl⟩ := hp
          have hlY : l ∈ Y := by
            have hh := Y.mul_mem hx (Y.inv_mem (hTY ht))
            simpa only [mul_inv_cancel_right] using hh
          have hlJ : (⟨l,hl⟩ : L) ∈ J.subgroupOf L := he.symm ▸ hlY
          exact B.mul_mem ⟨hLX hl,hlJ.2⟩ (hTB ht)
        exfalso
        apply hC.ne
        apply map_injective X.subtype_injective
        rw [map_subgroupOf_eq_of_le (show B ≤ X from inf_le_left)]
        exact le_antisymm hBY hYB
      · have hh := hmax.2 _ (lt_of_le_of_ne hJY he)
        intro l hl
        exact (show (⟨l,hl⟩ : L) ∈ Y.subgroupOf L from hh ▸ mem_top _)
    apply map_injective X.subtype_injective
    rw [← MonoidHom.range_eq_map,range_subtype]
    exact le_antisymm hYX (sup_le hLY hTY)


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
