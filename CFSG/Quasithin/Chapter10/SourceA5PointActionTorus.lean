module
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerTorus
public import Theory.Representation.NormalElementaryQuotient

/-!
# Excluding moving cubics on the constrained action quotient

The cubic residual identity puts every three-power element of the original
maximal local group into the component orbit. Its section centralizer fixes
the original moved module. A cubic in a component action quotient has a
three-power lift; the solvable kernel and the restricted two-kernel preserve
the original component normalizer and section-centralizer condition. Hence
that model cubic cannot move an original module vector under the literal
conjugation representation. The kernel need not be central or a two-group.

Source: Aschbacher–Smith, 10.2.9, printed pp.750–751, using 10.1.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The cubic residual argument applies to every three-power element. -/
theorem source_a5_threePower_sectionCentralizer_fixes_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {x : G} (hxM : x ∈ D.maximalLocal) (hx3 : ∃ n : ℕ, x ^ (3 ^ n) = 1)
    (hxL : x ∈ sectionCentralizer L) :
    x ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hx0 : x ∈ localOrbit T L := by
    rw [←source_nonnormal_cubic_residual D hn hd]
    let xM : D.maximalLocal := ⟨x,hxM⟩
    apply mem_map_of_mem D.maximalLocal.subtype (x := xM)
    obtain ⟨n,hn⟩ := hx3
    exact mem_primeToResidual_of_pow (n := n) (Subtype.ext hn)
  exact source_a5_orbit_sectionCentralizer_centralizes_moved D e hn ht htn hsep ⟨hx0,hxL⟩

omit [Finite G] in
private theorem sectionCentralizer_subgroupOf_map_le (I : Subgroup G) (hLI : L ≤ I) :
    (sectionCentralizer (L.subgroupOf I)).map I.subtype ≤ sectionCentralizer L := by
  have hc := (le_sectionCentralizer_iff (sectionCentralizer (L.subgroupOf I))
    (L.subgroupOf I)).mp le_rfl
  apply (le_sectionCentralizer_iff _ L).mpr
  constructor
  · have hn := (map_mono (f := I.subtype) hc.1).trans (le_normalizer_map I.subtype)
    rwa [map_subgroupOf_eq_of_le hLI] at hn
  · have hh := map_mono (f := I.subtype) hc.2
    rwa [map_commutator, map_pCoreIn_of_injective 2 _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hLI] at hh

/-- The exact model cubic has a preimage fixing the original moved module. -/
theorem source_a5_image_cubic_lifts_to_moved_centralizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hLI : L ≤ I)
    {Q : Type*} [Group Q] [Finite Q] (f : I →* Q) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker]
    (hkn : f.ker ≤ normalizer (L.subgroupOf I : Set I))
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    {x : Q} (hx3 : orderOf x = 3)
    (hxL : x ∈ sectionCentralizer ((L.subgroupOf I).map f)) :
    ∃ y : I, f y = x ∧ (y : G) ∈
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (L.subgroupOf I) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLI).symm.toMonoidHom) (subgroupOfEquivOfLe hLI).symm.surjective
  obtain ⟨y,hy,n,hnpow⟩ := f.exists_primePower_lift hf (p := 3) (n := 1)
    (by simpa only [pow_one] using hx3)
  have hyL : y ∈ sectionCentralizer (L.subgroupOf I) :=
    core_sectionCentralizer_comap_le f (L.subgroupOf I) hkn hk (by
      change f y ∈ sectionCentralizer ((L.subgroupOf I).map f)
      rwa [hy])
  have hyLG : (y : G) ∈ sectionCentralizer L :=
    sectionCentralizer_subgroupOf_map_le I hLI (mem_map_of_mem I.subtype hyL)
  refine ⟨y,hy,source_a5_threePower_sectionCentralizer_fixes_moved D e hn ht htn hsep ?_ ?_ hyLG⟩
  · exact hNL (((le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl).1 hyLG)
  · exact ⟨n,congrArg Subtype.val hnpow⟩

/-- Actual movement of an original moved vector contradicts the lifted
section-centralizer calculation, with the quotient representation retained. -/
theorem source_a5_no_moving_image_cubic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hLI : L ≤ I)
    {Q : Type*} [Group Q] [Finite Q] (f : I →* Q) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker]
    (hkn : f.ker ≤ normalizer (L.subgroupOf I : Set I))
    (hk : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (U : Subgroup I) [U.Normal] [IsElementaryAbelian 2 U]
    (hker : f.ker = centralizer (U : Set I))
    {x : Q} (hx3 : orderOf x = 3)
    (hxL : x ∈ sectionCentralizer ((L.subgroupOf I).map f))
    (w : U) (hw : ((w : I) : G) ∈ ⁅D.fullModule,L⁆)
    (hmove : Representation.NormalElementaryQuotient.representation U f hf hker x
      (Additive.ofMul w) ≠ Additive.ofMul w) : False := by
  obtain ⟨y,hy,hyC⟩ := source_a5_image_cubic_lifts_to_moved_centralizer
    D e hn ht htn hsep hNL I hLI f hf hkn hk hx3 hxL
  apply hmove
  rw [←hy]
  have ha := Representation.NormalElementaryQuotient.representation_apply U f hf hker
    y (Additive.ofMul w)
  have hc : y * (w : I) * y⁻¹ = (w : I) := by
    apply Subtype.ext
    change (y : G) * ((w : I) : G) * (y : G)⁻¹ = ((w : I) : G)
    rw [←hyC _ hw,mul_inv_cancel_right]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact ha.trans hc

end CFSG.Quasithin.Chapter10
