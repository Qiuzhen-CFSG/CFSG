module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.FixedLayer
public import Theory.Representation.SLThreeCentralExtension.CoverOrbits
public import Theory.GroupTheory.ConjugationOrbitSize
public import Theory.GroupAction.LargeOrbitSylow
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Saturated points of the positive binary-three cover

The original central kernel has order two. The fourteen vectors outside it
form one component orbit; the two original moved factors give a maximal-local
orbit of size twenty-eight. For a locally Sylow-saturated opposite point,
orbit-stabilizer therefore gives index four in T and index two in N_T(L).
The point, ambient Sylow and quotient action are unchanged throughout.
The final theorem applies this to PointSylowControl, retaining the source
omega-center geometry for this same selection owner to prove.
Source: Aschbacher--Smith, B.4.8 and 10.2.8--9, pp.91,749--750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The positive fixed kernel is the original subgroup of order two. -/
theorem moved_fixed_card_eq_two (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) : Nat.card (sourceMovedFixed D) = 2 := by
  have hlo := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hhi := moved_fixed_card_le_two D hmodel
  omega

/-- The original moved factor has sixteen elements in the positive-kernel row. -/
theorem moved_card_eq_sixteen (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) : Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 16 := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
  have hc := c.card_section
  change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) =
    Nat.card (Fin 3 → ZMod 2) * Nat.card (sourceMovedFixed D) at hc
  rw [moved_fixed_card_eq_two D ⟨e,⟨c⟩⟩ hne] at hc
  norm_num [Nat.card_fun,Nat.card_zmod,Nat.card_fin] at hc
  exact hc

/-- The fourteen nonfixed vectors form one orbit under the original component. -/
theorem moved_transitive_of_positive_kernel (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥)
    {u v : G} (hu : u ∈ ⁅D.fullModule,L⁆) (hv : v ∈ ⁅D.fullModule,L⁆)
    (hu0 : u ∉ centralizer (L : Set G)) (hv0 : v ∉ centralizer (L : Set G)) :
    ∃ l ∈ L, (MulAut.conj l) u = v := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
  let W := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ,hσ⟩ := BinaryConjugationSection.exists_action_of_central_kernel
    L W (normalizer_commutator_ge_right _ _) π hπ (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  obtain ⟨p,hp,hpcoord⟩ := c.exists_cover_of_fully_moved (specialLinearNatural 3) π hπ σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hker (w : Additive W) : p w = 0 ↔ (w.toMul : G) ∈ sourceMovedFixed D := by
    rw [hpcoord w]
    exact c.coordinates_eq_one_iff w.toMul
  have hpk : p.toLinearMap.ker ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    intro z hzK
    let w : Additive W := Additive.ofMul ⟨z,hzK.1⟩
    have hw : w ∈ p.toLinearMap.ker := (hker w).mpr hzK
    have hw0 : w = 0 := (show w ∈ (⊥ : Submodule (ZMod 2) (Additive W)) from hz ▸ hw)
    exact mem_bot.mpr (congrArg (fun a : Additive W => (a.toMul : G)) hw0)
  let a : Additive W := Additive.ofMul ⟨u,hu⟩
  let b : Additive W := Additive.ofMul ⟨v,hv⟩
  obtain ⟨g,hg⟩ := OneCohomology.SLThreeCentralExtension.transitive_outside_kernel_of_cover
    p hp hpk a b (fun h => hu0 ((hker a).mp h).2) (fun h => hv0 ((hker b).mp h).2)
  obtain ⟨l,hl⟩ := hπ g
  refine ⟨l,l.property,?_⟩
  have hh := congrArg (fun a : Additive W => (a.toMul : G)) hg
  rw [←hl,hσ] at hh
  exact hh

/-- Transport of the positive-kernel orbit to the specified opposite moved factor. -/
theorem partner_transitive_of_positive_kernel (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) (t : G)
    {u v : G} (hu : u ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hu0 : u ∉ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G))
    (hv0 : v ∉ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    ∃ l ∈ L.map (MulAut.conj t).toMonoidHom, (MulAut.conj l) u = v := by
  obtain ⟨a,ha,rfl⟩ := hu
  obtain ⟨b,hb,rfl⟩ := hv
  have han : a ∉ centralizer (L : Set G) := by
    intro h
    apply hu0
    change _ ∈ centralizer ((MulAut.conj t) '' (L : Set G))
    rw [←Theory.GroupTheory.map_centralizer_equiv]
    exact mem_map_of_mem (MulAut.conj t).toMonoidHom h
  have hbn : b ∉ centralizer (L : Set G) := by
    intro h
    apply hv0
    change _ ∈ centralizer ((MulAut.conj t) '' (L : Set G))
    rw [←Theory.GroupTheory.map_centralizer_equiv]
    exact mem_map_of_mem (MulAut.conj t).toMonoidHom h
  obtain ⟨l,hl,hab⟩ := moved_transitive_of_positive_kernel D hmodel hne ha hb han hbn
  refine ⟨(MulAut.conj t) l,mem_map_of_mem (MulAut.conj t).toMonoidHom hl,?_⟩
  change (t*l*t⁻¹)*(t*a*t⁻¹)*(t*l*t⁻¹)⁻¹ = t*b*t⁻¹
  have hh := congrArg (MulAut.conj t) hab
  simpa only [MulAut.conj_apply,map_mul,map_inv,MulEquiv.coe_toMonoidHom] using hh

/-- The positive-kernel orbit under L has exactly fourteen elements. -/
theorem moved_orbit_card_of_positive_kernel (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) {v : G} (hv : v ∈ ⁅D.fullModule,L⁆)
    (hv0 : v ∉ centralizer (L : Set G)) :
    (conjugacyOrbit L v).ncard = 14 := by
  have he : conjugacyOrbit L v =
      (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) \ (sourceMovedFixed D : Set G) := by
    ext w
    constructor
    · rintro ⟨l,rfl⟩
      have hn := normalizer_commutator_ge_right D.fullModule L l.property
      have hw := (mem_normalizer_iff.mp hn v).mp hv
      refine ⟨hw,?_⟩
      intro hc
      apply hv0
      have hh := (mem_normalizer_iff.mp
        ((normalizer_le_normalizer_centralizer L) (L.le_normalizer l.property)) v).mpr hc.2
      exact hh
    · intro hw
      obtain ⟨l,hl,he⟩ := moved_transitive_of_positive_kernel D hmodel hne hv hw.1 hv0
        (fun hc => hw.2 ⟨hw.1,hc⟩)
      exact ⟨⟨l,hl⟩,he⟩
  rw [he,Set.ncard_sdiff (show (sourceMovedFixed D : Set G) ⊆
    (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) from inf_le_left)]
  change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) - Nat.card (sourceMovedFixed D) = 14
  rw [moved_card_eq_sixteen D hmodel hne,moved_fixed_card_eq_two D hmodel hne]

/-- The maximal local group fuses the two disjoint fourteen-vector component orbits. -/
theorem local_orbit_card_of_positive_kernel (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) (hv0 : v ∉ centralizer (L : Set G)) :
    (conjugacyOrbit D.maximalLocal v).ncard = 28 := by
  let W := ⁅D.fullModule,L⁆
  let K := sourceMovedFixed D
  let X : Set G := (W : Set G) \ (K : Set G)
  let f := MulAut.conj t
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have htM := le_normalizer_componentOrbit L T ht
  have hmaps (m : G) (hm : m ∈ D.maximalLocal) :
      W.map (MulAut.conj m).toMonoidHom = ⁅D.fullModule,L.map (MulAut.conj m).toMonoidHom⁆ := by
    dsimp [W]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule hm)]
  have hKmaps (m : G) : K.map (MulAut.conj m).toMonoidHom =
      W.map (MulAut.conj m).toMonoidHom ⊓
        centralizer (L.map (MulAut.conj m).toMonoidHom : Set G) := by
    change (W ⊓ centralizer (L : Set G)).map _ = _
    rw [map_inf _ _ _ (MulAut.conj m).injective,Theory.GroupTheory.map_centralizer_equiv]
    rfl
  have himage (m : G) (hm : m ∈ D.maximalLocal) :
      (MulAut.conj m) '' X = X ∨ (MulAut.conj m) '' X = f '' X := by
    rcases source_nonnormal_maximal_pair D hn ht htn m hm with hl | hl
    · left
      have hw : W.map (MulAut.conj m).toMonoidHom = W := by rw [hmaps m hm,hl]
      have hk : K.map (MulAut.conj m).toMonoidHom = K := by rw [hKmaps m,hw,hl]; rfl
      change (MulAut.conj m) '' ((W : Set G) \ (K : Set G)) = _
      rw [Set.image_sdiff (MulAut.conj m).injective]
      change (W.map (MulAut.conj m).toMonoidHom : Set G) \ (K.map (MulAut.conj m).toMonoidHom : Set G) = X
      rw [hw,hk]
    · right
      have hw : W.map (MulAut.conj m).toMonoidHom = W.map f.toMonoidHom := by
        rw [hmaps m hm,hl,hmaps t htM]
      have hk : K.map (MulAut.conj m).toMonoidHom = K.map f.toMonoidHom := by
        rw [hKmaps m,hKmaps t,hw,hl]
      change (MulAut.conj m) '' ((W : Set G) \ (K : Set G)) =
        f '' ((W : Set G) \ (K : Set G))
      rw [Set.image_sdiff (MulAut.conj m).injective,Set.image_sdiff f.injective]
      change (W.map (MulAut.conj m).toMonoidHom : Set G) \ (K.map (MulAut.conj m).toMonoidHom : Set G) =
        (W.map f.toMonoidHom : Set G) \ (K.map f.toMonoidHom : Set G)
      rw [hw,hk]
  have hXM : X ⊆ conjugacyOrbit D.maximalLocal v := by
    intro w hw
    obtain ⟨l,hl,he⟩ := moved_transitive_of_positive_kernel D hmodel hne hv hw.1 hv0
      (fun hc => hw.2 ⟨hw.1,hc⟩)
    exact ⟨⟨l,((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) hl⟩,he⟩
  have he : conjugacyOrbit D.maximalLocal v = X ∪ f '' X := by
    apply Set.Subset.antisymm
    · rintro _ ⟨m,rfl⟩
      have hvX : v ∈ X := ⟨hv,fun h => hv0 h.2⟩
      have hmX : (MulAut.conj (m:G)) v ∈ (MulAut.conj (m:G)) '' X := ⟨v,hvX,rfl⟩
      rcases himage m m.property with hh | hh
      · exact Or.inl (hh ▸ hmX)
      · exact Or.inr (hh ▸ hmX)
    · rintro w (hw | ⟨x,hx,rfl⟩)
      · exact hXM hw
      · obtain ⟨m,hm⟩ := hXM hx
        refine ⟨⟨t*m,D.maximalLocal.mul_mem htM m.property⟩,?_⟩
        change (MulAut.conj (t*(m:G))) v = f x
        rw [map_mul,MulAut.mul_apply]
        change f ((m:G)*v*(m:G)⁻¹) = f x
        rw [show (m:G)*v*(m:G)⁻¹=x from hm]
  have hd : Disjoint X (f '' X) := by
    apply Set.disjoint_left.mpr
    rintro w hw ⟨x,hx,rfl⟩
    exact hw.2 ⟨hw.1,hcross (mem_map_of_mem f.toMonoidHom hx.1)⟩
  have hc : X.ncard = 14 := by
    dsimp [X]
    rw [Set.ncard_sdiff (show (K : Set G) ⊆ (W : Set G) from inf_le_left)]
    change Nat.card W - Nat.card K = 14
    rw [moved_card_eq_sixteen D hmodel hne,moved_fixed_card_eq_two D hmodel hne]
  rw [he,Set.ncard_union_eq hd,Set.ncard_image_of_injective _ f.injective,hc]

omit D in
private theorem point_sylow_index_of_orbit
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (v : G)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (M ⊓ centralizer ({v} : Set G))) :
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex (T : Subgroup G) =
      2 ^ (conjugacyOrbit M v).ncard.factorization 2 := by
  let S := T.subtype hTM
  let C := (centralizer ({v} : Set G)).subgroupOf M
  let R := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  have hCM : C.map M.subtype = M ⊓ centralizer ({v} : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hSM : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTM
  have hRM : ((S : Subgroup M) ⊓ C).map M.subtype = R := by
    rw [map_inf _ _ _ M.subtype_injective,hSM,hCM,←inf_assoc,inf_eq_left.mpr hTM]
  have hodd : ¬ 2 ∣ ((S : Subgroup M) ⊓ C).relIndex C := by
    have he := relIndex_map_map_of_injective ((S : Subgroup M) ⊓ C) C M.subtype_injective
    rw [hRM,hCM] at he
    rw [←he]
    obtain ⟨P,hP⟩ := hs
    have hp : ¬ 2 ∣ R.relIndex (M ⊓ centralizer ({v} : Set G)) := by
      change ¬ 2 ∣ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex _
      rw [←hP]
      simpa only [relIndex,subgroupOf,comap_map_eq_self_of_injective
        (M ⊓ centralizer ({v} : Set G)).subtype_injective] using P.not_dvd_index
    exact hp
  have he := sylow_inf_index_of_odd_relative_index S C hodd
  have hi := relIndex_map_map_of_injective ((S : Subgroup M) ⊓ C)
    (S : Subgroup M) M.subtype_injective
  rw [hRM,hSM] at hi
  rw [hi,he]
  congr 1
  let : MulAction M G := MulAction.compHom G (MulAut.conj.comp M.subtype)
  have hstab : MulAction.stabilizer M v = C := by
    ext m
    change (m:G)*v*(m:G)⁻¹=v ↔ (m:G) ∈ centralizer ({v} : Set G)
    rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
  rw [←hstab,MulAction.index_stabilizer]
  rfl

/-- A saturated nonfixed point has index four in T in the positive-kernel row. -/
theorem partner_point_sylow_index_four
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex (T : Subgroup G) = 4 := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) inf_le_right ht htn
  have hvB : v ∉ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
    intro h
    apply hv0
    have hc : L ⊔ L.map (MulAut.conj t).toMonoidHom ≤ centralizer ({v} : Set G) :=
      sup_le (fun l hl => mem_centralizer_singleton_iff.mpr (hcross hv l hl))
        (fun l hl => mem_centralizer_singleton_iff.mpr (h l hl))
    rw [←hpair] at hc
    exact fun l hl => mem_centralizer_singleton_iff.mp (hc hl)
  obtain ⟨w,hw,hwv⟩ := hv
  have hw0 : w ∉ centralizer (L : Set G) := by
    intro h
    apply hvB
    rw [←hwv]
    change _ ∈ centralizer ((MulAut.conj t) '' (L : Set G))
    rw [←Theory.GroupTheory.map_centralizer_equiv]
    exact mem_map_of_mem (MulAut.conj t).toMonoidHom h
  have ho : (conjugacyOrbit D.maximalLocal v).ncard = 28 := by
    rw [←hwv]
    exact (conjugacyOrbit_normalizer D.maximalLocal w t
      (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T ht))).trans
      (local_orbit_card_of_positive_kernel D hmodel hne ht htn hcross hw hw0)
  rw [point_sylow_index_of_orbit D.maximalLocal (le_normalizer_componentOrbit L T) v hs,ho]
  have hf : (28 : ℕ).factorization 2 = 2 := by
    rw [show (28 : ℕ) = 2 ^ 2 * 7 from rfl,
      Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
  rw [hf]
  norm_num

/-- The positive-kernel point Sylow is a subgroup of index two in the original
half-Sylow, with no change of point or of the chosen ambient Sylow subgroup. -/
theorem partner_point_sylow_index_two_in_half_sylow
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) = 2 := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hRS : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G) := le_inf inf_le_left
    ((inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D hn (hcross hv) hv0))
  have he := relIndex_mul_relIndex _ _ _ hRS (show
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) from inf_le_left)
  rw [partner_point_sylow_index_four D hmodel hne ht htn hcross hv hv0 hs,
    inf_relIndex_left,source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn] at he
  omega
/-- The literal component quotient in the binary-three row is divisible by three. -/
theorem three_dvd_quotient (hmodel : BinaryThreeNatural D) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨e,_⟩ := hmodel
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
  decide

/-- Half-Sylow uniqueness removes the fixed-vector exception before applying
the exact positive-kernel index calculation to the original escaping point. -/
theorem escaping_point_indices_of_positive_kernel
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    v ∉ centralizer (localOrbit T L : Set G) ∧
    (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) ∧
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex (T : Subgroup G) = 4 ∧
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) = 2 := by
  obtain ⟨hv0,hstab⟩ := Selection.escaping_point_stabilizes D hhalf
    (fixed_layer_centralizes_half_sylow D hmodel ht htn hcross) ht htn hcross hv hvne hout
  exact ⟨hv0,hstab,partner_point_sylow_index_four D hmodel hne ht htn hcross hv hv0 hs,
    partner_point_sylow_index_two_in_half_sylow D hmodel hne ht htn hcross hv hv0 hs⟩

/-- Application to the literal point-control consumer. Only the omega-center
and perfect-residual identities of 10.2.8 remain; their point has now been
proved to have index two in the original half-Sylow. The selection owner
qt-d-10-nona5-point-selection retains discharge of these two identities. -/
theorem pointSylowControl_of_positive_kernel_omega_geometry
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hZ : localOrbit T L ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G))
    (hres : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
      v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
      ¬ centralizer ({v} : Set G) ≤ D.maximalLocal →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex
        ((T : Subgroup G) ⊓ normalizer (L : Set G)) = 2 →
      cubicPerfectCore (localOrbit T L ⊓ centralizer
        (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) = L) :
    PointSylowControl D t := by
  intro v hv hvne hout hs
  obtain ⟨hv0,hstab,_,hi⟩ := escaping_point_indices_of_positive_kernel D
    hmodel hne hhalf ht htn hcross hv hvne hout hs
  refine ⟨?_,hstab⟩
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu (partner_le_fullModule D ht hv)
  have hZle : omegaCenterIn (T : Subgroup G) ≤
      omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) := by
    intro z hz
    obtain ⟨hzT,hzc,hz2⟩ := (mem_omegaCenterIn_iff _ _).mp hz
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨⟨hzT,mem_centralizer_singleton_iff.mpr (hzc v hvT).symm⟩,
        centralizer_le inf_le_left hzc,hz2⟩
  exact point_normalizer_le_of_omega_residual D (fun hn => htn (hn ht))
    hhalf (three_dvd_quotient D hmodel) hZ v hZle (hres v hv hvne hv0 hout hs hi)

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
