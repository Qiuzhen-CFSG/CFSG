module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.CartanIntersection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Generation
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.Quasithin.CoprimeRank

/-!
# The original Cartan inside the symplectic triangle vertex

The point and plane determinant characters identify the original symplectic
Cartan with the product of two field-unit groups. Their common kernel is a
two-group, so the odd Cartan injects; the known Cartan order makes the map
surjective. The two character kernels are precisely the intersections with
the original residuals L₁ and L₂. To lift this assertion, the original
O₂(L) normalizes both residuals and an odd subgroup absorbs no extra part
of that two-group supplement.

Thus X = (X ∩ L₁)(X ∩ L₂), with trivial intersection of the factors. The
proved field-four identity X ∩ L₁ = X ∩ K₀ places X inside I = K₀ ∨ L₂.
A nontrivial common normal two-subgroup supplies the ambient upper bound
on three-rank, giving m₃(I) = m₃(I/O₂(I)) = 2. The final consumer supplies
that common subgroup from the retained nontrivial C_V(L) and combines the
rank calculation with the existing relatively normal component construction.

All flags and residuals use the original quotient and natural action marking.
No central part of V is discarded. This discharges the Cartan-containment
and rank premises of the recognition step in the symplectic branch. The
faithful fixed-layer common-normal argument, the other initial model branches,
recognition of I, the SL₃(4) exclusion and both orientations remain with
qt-d-1222-natural-relative-components. Earlier flag/Cartan and preliminary
inputs retain their original producers and final discharge in
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--763, especially X = X_K(X ∩ L₂) and m₃(I) = 2.
-/

set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {A B : Type*} [Group A] [Group B] [Finite A]

omit [Finite A] in
private theorem odd_isTwoPerfect (U : Subgroup A) (ho : Odd (Nat.card U)) :
    IsPPerfect 2 U := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (U ⧸ N) = 1
  exact htwo.card_eq_or_dvd.resolve_right
    (fun hd => ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))

omit [Finite A] in
/-- An odd subgroup sees the actual residual lift, not only its image. -/
private theorem odd_inf_comap_map (q : A →* B) (hk : IsPGroup 2 q.ker)
    (R X : Subgroup A) (ho : Odd (Nat.card X))
    (hn : q.ker ≤ normalizer (R : Set A)) :
    X ⊓ (R.map q).comap q = X ⊓ R := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    apply le_of_isPPerfect_of_le_sup_of_normalizes
      (X ⊓ (R.map q).comap q) R q.ker
      (odd_isTwoPerfect _ (ho.of_dvd_nat (card_dvd_of_le inf_le_left))) hk hn
    simpa only [comap_map_eq] using
      (inf_le_right : X ⊓ (R.map q).comap q ≤ (R.map q).comap q)
  · exact inf_le_inf_left X (le_comap_map _ _)

private theorem residual_map_equiv (e : B ≃* B) [Finite B] (P : Subgroup B) :
    (solvableResidual (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype =
      ((solvableResidual P).map P.subtype).map e.toMonoidHom := by
  have hc : (P.map e.toMonoidHom).comap e.toMonoidHom = P := by
    rw [comap_map_eq, e.toMonoidHom.ker_eq_bot e.injective, sup_bot_eq]
  have h := map_solvableResidual_comap e.toMonoidHom e.surjective (P.map e.toMonoidHom)
  rw [hc] at h
  exact h.symm

omit [Finite A] in
/-- Two independent scalar characters give the two original Cartan factors. -/
private theorem split_of_product_equiv {C E : Type*} [Group C] [Group E]
    (X R₀ R₁ : Subgroup A) (e : X ≃* C × E)
    (h₀ : ∀ x : X, (e x).1 = 1 ↔ (x : A) ∈ R₀)
    (h₁ : ∀ x : X, (e x).2 = 1 ↔ (x : A) ∈ R₁) :
    (X ⊓ R₀) ⊔ (X ⊓ R₁) = X ∧ Disjoint (X ⊓ R₀) (X ⊓ R₁) := by
  constructor
  · apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    let a := e.symm (1,(e ⟨x,hx⟩).2)
    let b := e.symm ((e ⟨x,hx⟩).1,1)
    have ha : (a : A) ∈ X ⊓ R₀ := ⟨a.property,(h₀ a).mp (by simp [a])⟩
    have hb : (b : A) ∈ X ⊓ R₁ := ⟨b.property,(h₁ b).mp (by simp [b])⟩
    have hab : (a : A) * b = x := by
      change ((a*b : X) : A) = x
      have he : a*b = ⟨x,hx⟩ := e.injective (by simp [a,b])
      exact congrArg Subtype.val he
    rw [←hab]
    exact mul_mem_sup ha hb
  · apply disjoint_def.mpr
    intro x hx hy
    have he : e ⟨x,hx.1⟩ = 1 := Prod.ext ((h₀ _).mpr hx.2) ((h₁ _).mpr hy.2)
    exact congrArg Subtype.val (e.map_eq_one_iff.mp he)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

open Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.Sp4
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private abbrev c := Coordinates.sp4 m
private abbrev f := LocalGeometry.Sp4.flag m S
private abbrev a := MulAut.conj (LocalGeometry.Sp4.alignment m)
private abbrev r : L →* Sp S.field.Carrier := (a S m).symm.toMonoidHom.comp (c S m).quotientMap

private theorem r_ker : (r S m).ker = pCore 2 L := by
  ext x
  change (a S m).symm ((c S m).groupEquiv (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ _
  rw [(a S m).symm.map_eq_one_iff]
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
  rw [m.groupEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

private theorem residual_image (i : Fin 2) :
    (((f S m).Li i).subgroupOf L).map (r S m) =
      LocalGeometry.Sp4.standardLocal (F := S.field) i := by
  rw [r, ←map_map]
  change (((localResidual L ((c S m).preimage
    (LocalGeometry.Sp4.space m i.castSucc.succ))).subgroupOf L).map
      (c S m).quotientMap).map (a S m).symm.toMonoidHom = _
  rw [LocalGeometry.Sp4.localResidual_image,LocalGeometry.Sp4.modelStabilizer_space]
  change ((solvableResidual ((stabilizer (LocalGeometry.Sp4.ModelFlag.stage
    (F := S.field.Carrier) i.castSucc.succ)).map (a S m).toMonoidHom)).map
      ((stabilizer (LocalGeometry.Sp4.ModelFlag.stage (F := S.field.Carrier)
        i.castSucc.succ)).map (a S m).toMonoidHom).subtype).map
          (a S m).symm.toMonoidHom = _
  rw [residual_map_equiv,map_map]
  have he : (a S m).symm.toMonoidHom.comp (a S m).toMonoidHom = MonoidHom.id _ := by
    ext x : 1
    exact (a S m).symm_apply_apply x
  rw [he,map_id]
  fin_cases i
  · exact pointParabolic_solvableResidual_eq S.field.card_eq S.nonbinary
  · exact planeParabolic_solvableResidual_eq S.field.card_eq S.nonbinary

private theorem cartan_borel {X : Subgroup G} (hX : IsCartan T L X) (x : X) :
    r S m ⟨x,(hX.1 x.property).1⟩ ∈ Theory.SpecificGroups.SymplecticFour.borel := by
  have hn (i : Fin 2) : (c S m).quotientMap ⟨x,(hX.1 x.property).1⟩ ∈
      (c S m).modelStabilizer (LocalGeometry.Sp4.space m i.castSucc.succ) := by
    exact ((c S m).mem_normalizer_preimage_iff _ _).mp
      ((f S m).cartan_normalizes (LocalGeometry.Sp4.flag_inner_unique m S) hX i.castSucc x.property)
  have hh (i : Fin 2) : r S m ⟨x,(hX.1 x.property).1⟩ ∈
      stabilizer (LocalGeometry.Sp4.ModelFlag.stage (F := S.field.Carrier) i.castSucc.succ) := by
    have h := hn i
    rw [LocalGeometry.Sp4.modelStabilizer_space,mem_map_equiv] at h
    exact h
  exact ⟨hh 0,hh 1⟩

private def characters {X : Subgroup G} (hX : IsCartan T L X) :
    X →* S.field.Carrierˣ × S.field.Carrierˣ :=
  borelCharacters.comp (((r S m).comp (inclusion (hX.1.trans inf_le_left))).codRestrict
    Theory.SpecificGroups.SymplecticFour.borel (cartan_borel S m hX))

private theorem characters_injective {X : Subgroup G} (hX : IsCartan T L X) :
    Function.Injective (characters S m hX) := by
  let q := (r S m).comp (inclusion (hX.1.trans inf_le_left))
  have hkq : IsPGroup 2 q.ker := by
    change IsPGroup 2 ((r S m).ker.comap (inclusion (hX.1.trans inf_le_left)))
    rw [r_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have ho : Odd (Nat.card q.ker) := hX.odd.of_dvd_nat (card_subgroup_dvd_card _)
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    (card_eq_one.mp (hkq.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hu : q x ∈ unipotent := (borelCharacters_eq_one
    ⟨q x,cartan_borel S m hX x⟩).mp hx
  have hc : IsPGroup 2 (Subgroup.zpowers (q x)) :=
    (isPGroup_unipotent S.field.card_eq).to_le (zpowers_le.mpr hu)
  have hod : Odd (Nat.card (Subgroup.zpowers (q x))) := by
    rw [Nat.card_zpowers]
    exact hX.odd.of_dvd_nat ((orderOf_map_dvd q x).trans (orderOf_dvd_natCard (x := x)))
  have hz : q x = 1 := by
    have he : Subgroup.zpowers (q x) = ⊥ :=
      card_eq_one.mp (hc.card_eq_or_dvd.resolve_right hod.not_two_dvd_nat)
    exact he.le (mem_zpowers (q x))
  exact hq (hz.trans q.map_one.symm)

private theorem characters_membership {X : Subgroup G} (hX : IsCartan T L X)
    (i : Fin 2) (x : X) :
    (if i = 0 then (characters S m hX x).1 else (characters S m hX x).2) = 1 ↔
      (x : G) ∈ (f S m).Li i := by
  have hle : (f S m).Li i ≤ L := (localResidual_le _).trans inf_le_left
  have hkN : (r S m).ker ≤ normalizer (((f S m).Li i).subgroupOf L : Set L) := by
    rw [r_ker,← subgroupOf_normalizer_eq hle]
    have hp : pCore 2 L ≤ (T : Subgroup G).subgroupOf L := by
      rw [←(c S m).innerSylow_coe]
      exact pCore_isPGroup.le_sylow_of_normal _
    exact hp.trans (comap_mono ((f S m).sylow_normalizes_Li i))
  have he := odd_inf_comap_map (r S m)
    (by rw [r_ker]; exact pCore_isPGroup)
    (((f S m).Li i).subgroupOf L) (X.subgroupOf L)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe (hX.1.trans inf_le_left)).toEquiv]; exact hX.odd) hkN
  rw [residual_image] at he
  have hmem : r S m ⟨x,(hX.1 x.property).1⟩ ∈ LocalGeometry.Sp4.standardLocal (F := S.field) i ↔
      (x : G) ∈ (f S m).Li i := by
    constructor
    · intro hx
      exact (he.le ⟨x.property,hx⟩).2
    · intro hx
      exact (he.ge ⟨x.property,hx⟩).2
  rw [←hmem]
  fin_cases i
  · change (determinantCharacter (point S.field.Carrier) _ = 1) ↔ _ ∈ pointLocal
    rw [pointLocal,mem_determinantKernel_iff]
    exact ⟨fun h => ⟨(cartan_borel S m hX x).1,h⟩,fun h => h.choose_spec⟩
  · change (determinantCharacter (plane S.field.Carrier) _ = 1) ↔ _ ∈ planeLocal
    rw [planeLocal,mem_determinantKernel_iff]
    exact ⟨fun h => ⟨(cartan_borel S m hX x).2,h⟩,fun h => h.choose_spec⟩

/-- The original full symplectic Cartan splits into its two residual intersections. -/
theorem cartan_split {X : Subgroup G} (hX : IsCartan T L X) :
    (X ⊓ (LocalGeometry.Sp4.flag m S).Li 0) ⊔ (X ⊓ (LocalGeometry.Sp4.flag m S).Li 1) = X ∧
      Disjoint (X ⊓ (LocalGeometry.Sp4.flag m S).Li 0) (X ⊓ (LocalGeometry.Sp4.flag m S).Li 1) := by
  have hc : Nat.card X = Nat.card (S.field.Carrierˣ × S.field.Carrierˣ) := by
    rw [(c S m).cartan_card hX,Nat.card_prod,Nat.card_units,S.field.card_eq,pow_two]
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (S.field.Carrierˣ × S.field.Carrierˣ)
  have hb : Function.Bijective (characters S m hX) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨characters_injective S m hX,by simpa only [Nat.card_eq_fintype_card] using hc⟩
  exact split_of_product_equiv X _ _ (MulEquiv.ofBijective (characters S m hX) hb)
    (characters_membership S m hX 0) (characters_membership S m hX 1)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.Sp4


open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- Both residual intersections of the original symplectic Cartan generate it,
for every flag with the original Sylow invariance and literal preimages. -/
theorem sp4_cartan_split {X : Subgroup G} (hX : IsCartan T L X) :
    (X ⊓ f.Li 0) ⊔ (X ⊓ f.Li 1) = X ∧ Disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1) := by
  have he (i : Fin 3) : f.space i = (LocalGeometry.Sp4.flag m S).space i :=
    LocalGeometry.Sp4.flag_inner_unique m S i (f.space i) (f.dimension i)
      (inf_le_left.trans (f.invariant i))
  have hv (i : Fin 3) : f.Vi i = (LocalGeometry.Sp4.flag m S).Vi i :=
    congrArg (Coordinates.preimage (.sp4 m)) (he i)
  have hr (i : Fin 2) : f.Li i = (LocalGeometry.Sp4.flag m S).Li i :=
    congrArg (localResidual L) (hv i.castSucc)
  rw [hr 0,hr 1]
  exact Triangle.Sp4.cartan_split S m hX

/-- In the exceptional symplectic configuration the actual Cartan lies in
the third vertex I = K₀ ∨ L₂, without assuming common-normal existence. -/
theorem sp4_triangle_cartan_le_join
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    X ≤ K₀ ⊔ f.Li 1 := by
  obtain ⟨_,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  rw [←(sp4_cartan_split D S m f hX).1]
  exact sup_le_sup ((h₁.symm.trans h₀).le.trans inf_le_right) inf_le_right

/-- The third vertex and its literal two-core quotient have three-rank two
once the original common normal subgroup is supplied. -/
theorem sp4_triangle_join_three_rank
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    primeRank 3 (K₀ ⊔ f.Li 1 : Subgroup G) = 2 ∧
      primeRank 3 ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) = 2 := by
  have hXI := sp4_triangle_cartan_le_join D S m f hu hm₁ hfour hX hK hLK hK₀ hK₀K hk hp
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hn : K₀ ⊔ f.Li 1 ≤ normalizer (Q : Set G) := sup_le hKQ hLQ
  have hupp := (_root_.primeRank_le_of_injective 3 (inclusion hn)
    (inclusion_injective hn)).trans (hN.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hlo := _root_.primeRank_le_of_injective 3 (inclusion hXI) (inclusion_injective hXI)
  rw [(Coordinates.sp4 m).cartan_primeRank hX Nat.prime_three (by simp [hfour])] at hlo
  have he := le_antisymm hupp hlo
  exact ⟨he,(primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans he⟩

/-- The nontrivial fixed-layer branch supplies all the subgroup and rank
inputs for recognizing the third vertex. Its model recognition is not asserted. -/
theorem sp4_triangle_join_of_nontrivial_fixed_layer
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      X ≤ K₀ ⊔ f.Li 1 ∧ primeRank 3 (K₀ ⊔ f.Li 1 : Subgroup G) = 2 ∧
      primeRank 3 ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) = 2 := by
  obtain ⟨hI,hIL,hIH,_⟩ := triangle_join_component_of_nontrivial_fixed_layer
    D S f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hfixed
  have hKC : K ≤ centralizer (f.Vi 0 : Set G) :=
    subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl hm₁ hfix hK.1 hLK.le
  have hKCQ : K₀ ≤ normalizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    (hK₀K.le.trans (hKC.trans (centralizer_le (f.centralizer_le_Vi 0)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hLCQ : f.Li 1 ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le
      ((localResidual_le _).trans inf_le_left)))
  obtain ⟨hr,hrq⟩ := sp4_triangle_join_three_rank D S m f hu hm₁ hfour hX hK hLK
    hK₀ hK₀K hk hp hfixed (inf_le_left.trans D.le_sylow) hKCQ
    (hLCQ.trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨hI,hIL,hIH,sp4_triangle_cartan_le_join D S m f hu hm₁ hfour hX hK hLK
    hK₀ hK₀K hk hp,hr,hrq⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
