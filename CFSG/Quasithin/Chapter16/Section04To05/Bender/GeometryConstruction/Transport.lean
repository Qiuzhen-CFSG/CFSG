module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts
public import Theory.ElementaryAbelian.Join

/-!
# Normalizers and unitary transport in the Bender geometry

The unitary route uses the source Sylow placement and a component containment
`T_L ≤ L^g`. These force `T_L^g = T_L` by finite cardinality. The earlier
Sylow upgrade identifies `R = T_C^g`; once the model calculation places
`Ω₁(R)` in `V`, the same cardinality argument gives `V^g = V`.

The remaining lemmas derive Sylow normalization, the centralizer intersection,
and relative normality of the actor image from the actual component action
image. No disjointness of `Ω₁(T_C)` and `Ω₁(T_L)` is used, so the exceptional
Suzuki cover remains permitted. Constructing the cyclic actor and establishing
the model-dependent containment and image equality are separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed pp.1194–1195, using 16.4.2(4) and 16.4.10–11.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem component_normalizes_centralizer (L : Subgroup G) :
    L ≤ normalizer (centralizer (L : Set G) : Set G) :=
  (le_centralizer_iff.mp le_rfl).trans (centralizer_le_normalizer _)

omit [Finite G] in
/-- Normalizing a subgroup preserves its first omega subgroup. -/
theorem normalizer_le_omega_normalizer (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (omegaOneAmbient P : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (omegaOneAmbient P).map (MulAut.conj g).toMonoidHom = _
  have he : P.map (MulAut.conj g).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rw [← omega_map_equiv, he]

/-- The source Sylow transport and containment in the conjugate component force preservation of T_L. -/
theorem componentSylow_preserved {T : Sylow 2 G} {L : Subgroup G} {g : G}
    (hplace : componentSylow T L ≤ L.conjBy g)
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    g ∈ normalizer (componentSylow T L : Set G) := by
  have hn : L.conjBy g ≤
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      (component_normalizes_centralizer L)
    rw [map_equiv_normalizer_eq] at hh
    exact hh
  have hle : componentSylow T L ≤ (componentSylow T L).conjBy g := by
    change componentSylow T L ≤ ((T : Subgroup G) ⊓ L).map _
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    exact le_inf ((le_inf inf_le_left (hplace.trans hn)).trans htransport) hplace
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hle
    (card_map_of_injective (MulAut.conj g).injective).le).symm

/-- Construct all moving-conjugator fields in the unitary route from source placement and omega containment. -/
theorem unitary_transport {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hplace : componentSylow T L ≤ L.conjBy g)
    (hU : omegaOneAmbient R ≤ benderSpace T L) :
    g ∈ normalizer (componentSylow T L : Set G) ∧
    g ∈ normalizer (benderSpace T L : Set G) ∧
    (omegaOneAmbient (commutingSylow T L)).conjBy g = omegaOneAmbient R := by
  have hTL := componentSylow_preserved hplace htransport
  have hUC := (omega_conjugate (h.eq_conjugate_commutingSylow hR htransport)).symm
  have hUL : (omegaOneAmbient (componentSylow T L)).conjBy g =
      omegaOneAmbient (componentSylow T L) := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_omega_normalizer (componentSylow T L) hTL)
  have hV : (benderSpace T L).conjBy g ≤ benderSpace T L := by
    change ((omegaOneAmbient (commutingSylow T L)) ⊔
      omegaOneAmbient (componentSylow T L)).map _ ≤ _
    rw [Subgroup.map_sup]
    change (omegaOneAmbient (commutingSylow T L)).conjBy g ⊔
      (omegaOneAmbient (componentSylow T L)).conjBy g ≤ _
    rw [hUC, hUL]
    exact sup_le hU le_sup_right
  refine ⟨hTL, mem_normalizer_iff_map_conj_eq.mpr ?_, hUC⟩
  exact eq_of_le_of_card_ge hV
    (card_map_of_injective (MulAut.conj g).injective).ge

/-- Tight embedding forces every stabilizer of U_C to normalize the component. -/
theorem commuting_omega_stabilizer {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) :
    normalizer (omegaOneAmbient (commutingSylow T L) : Set G) ≤
      normalizer (L : Set G) := by
  rw [← h.normalizers_eq]
  exact h.tight.normalizer_le
    (T.isPGroup'.of_injective
      (inclusion ((omegaOneAmbient_le _).trans inf_le_left)) (inclusion_injective _))
    (commuting_omega_nontrivial h) ((omegaOneAmbient_le _).trans inf_le_right)

/-- The actual ambient Sylow subgroup normalizes both V and U_C. -/
theorem sylow_normalizes_factors {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : StandardSetup T z L) :
    (T : Subgroup G) ≤ normalizer (benderSpace T L : Set G) ∧
    (T : Subgroup G) ≤ normalizer (omegaOneAmbient (commutingSylow T L) : Set G) := by
  have hTL : (T : Subgroup G) ≤ normalizer (componentSylow T L : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hTC : (T : Subgroup G) ≤ normalizer (commutingSylow T L : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer (h.normalizers_eq ▸ h.sylow_normalizes)).trans
      inf_normalizer_le_normalizer_inf
  have hUC := hTC.trans (normalizer_le_omega_normalizer _)
  refine ⟨?_, hUC⟩
  exact (le_inf hUC (hTL.trans (normalizer_le_omega_normalizer _))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)


omit [Finite G] in
/-- An actor in N_L(T_L) normalizes the actual subgroup V. -/
theorem actor_normalizes_space {T : Sylow 2 G} {L X : Subgroup G}
    (hX : X ≤ L ⊓ normalizer (componentSylow T L : Set G)) :
    X ≤ normalizer (benderSpace T L : Set G) := by
  have hXC : X ≤ centralizer (omegaOneAmbient (commutingSylow T L) : Set G) :=
    le_centralizer_iff.mp (((omegaOneAmbient_le _).trans inf_le_right).trans
      (centralizer_le (hX.trans inf_le_left)))
  exact (le_inf (hXC.trans (centralizer_le_normalizer _))
    ((hX.trans inf_le_right).trans (normalizer_le_omega_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
/-- The fixed subgroup calculation also identifies V ∩ C_G(L). -/
theorem fixed_intersection_of_fixed_eq {T : Sylow 2 G} {L X : Subgroup G}
    (hXL : X ≤ L)
    (hfixed : benderSpace T L ⊓ centralizer (X : Set G) =
      omegaOneAmbient (commutingSylow T L)) :
    omegaOneAmbient (commutingSylow T L) =
      benderSpace T L ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · exact le_inf le_sup_left ((omegaOneAmbient_le _).trans inf_le_right)
  · rw [← hfixed]
    exact inf_le_inf_left _ (centralizer_le hXL)

/-- Equality with the component action image proves relative normality in the stabilizer of U_C. -/
theorem actor_normal_in_stabilizer_of_image {T : Sylow 2 G} {z : G} {L X : Subgroup G}
    (h : StandardSetup T z L)
    (himage : inducedActor (benderSpace T L) X = inducedActor (benderSpace T L) L)
    (a : normalizer (benderSpace T L : Set G))
    (ha : (a : G) ∈ normalizer (omegaOneAmbient (commutingSylow T L) : Set G)) :
    (inducedActor (benderSpace T L) X).conjBy
      ((benderSpace T L).normalizerMonoidHom.rangeRestrict a) =
        inducedActor (benderSpace T L) X := by
  rw [himage]
  apply mem_normalizer_iff_map_conj_eq.mp
  apply le_normalizer_map (benderSpace T L).normalizerMonoidHom.rangeRestrict
  refine ⟨a, ?_, rfl⟩
  exact le_normalizer_comap (normalizer (benderSpace T L : Set G)).subtype
    (commuting_omega_stabilizer h ha)

omit [Finite G] in
/-- The two omega subgroups commute, even when their intersection is nontrivial. -/
theorem space_elementary_of_factors {T : Sylow 2 G} {L : Subgroup G}
    [IsElementaryAbelian 2 (omegaOneAmbient (commutingSylow T L))]
    [IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L))] :
    IsElementaryAbelian 2 (benderSpace T L) :=
  IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp
      (((omegaOneAmbient_le _).trans inf_le_right).trans
        (centralizer_le ((omegaOneAmbient_le _).trans inf_le_right))))

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
