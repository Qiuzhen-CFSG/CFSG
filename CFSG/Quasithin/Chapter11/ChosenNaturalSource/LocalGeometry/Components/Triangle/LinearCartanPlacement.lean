module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearThirdVertex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LocalGLSp4


/-!
# Cartan placement for the original linear triangle

Use the one aligned quotient of the original SL₃ natural flag. The first
and last diagonal characters of its Borel identify the odd Cartan with
Fˣ × Fˣ. Their kernels lift to the actual residuals L₁ and L₂: the
original two-core normalizes these residuals, so oddness removes the
two-group supplement. Thus X = (X ∩ L₁)(X ∩ L₂), with trivial intersection.
The proved equality X ∩ L₁ = X ∩ K₀ places X in I = K₀ ∨ L₂ without
assuming a common normal subgroup.

The same splitting makes both residuals proper in I and gives their cubic
Cartan intersections. The checked index-three local theorem then supplies
both GL₂(4) quotients, retaining each smaller embedded residual two-core.
The literal common-Q consumer constructs relative normality and local/He
membership, both three-ranks, and excludes SL₃(4) for this third vertex.
In particular its Cartan-containment premise is now discharged.

Existence of Q, recognition of the remaining linear-branch third-vertex
models, the Weyl normalizer escape, exclusion of the original SL₃(4)
vertex, both triangle orientations and full 11.1.1--3 remain with
qt-d-1222-natural-relative-components. The original flag/Cartan and
earlier-source inputs retain their producers and final discharge in
qt-d-1222-natural-local-geometry. No module comparison or common-normal
existence is inferred from these conditional results.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 11.1.2,
printed pp.762--763, the Cartan product and the two GL₂(4) markings.
-/

set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open SL3.PlaneAction

private def borelCharacters {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) : borelSL F →* Fˣ × Fˣ :=
  (BorelQuotient.quotientSLTorusEquiv F hF).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (borelSL F)))

private theorem borelCharacters_ker {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) : (borelCharacters hF).ker = pCore 2 (borelSL F) := by
  rw [borelCharacters,MonoidHom.ker_comp_of_injective _ _
    (BorelQuotient.quotientSLTorusEquiv F hF).injective,QuotientGroup.ker_mk']

private theorem borelCharacters_local {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (i : Fin 2) (g : borelSL F) :
    (if i = 0 then (borelCharacters hF g).1 else (borelCharacters hF g).2) = 1 ↔
      g.val ∈ localGroup (F := F) i := by
  obtain ⟨d,u,hu,he⟩ := BorelQuotient.borelSL_factorization F g g.property
  let u' : borelSL F := ⟨u,unipotentSL_le_borelSL F hu⟩
  let t : borelSL F := ⟨torusSL F d,BorelQuotient.torusSL_mem_borel F d⟩
  have hg : g = u' * t := Subtype.ext he
  have hc : borelCharacters hF g = d := by
    rw [hg,map_mul]
    have hz : borelCharacters hF u' = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [borelCharacters_ker,BorelQuotient.twoCoreSL_eq F hF]
      exact hu
    rw [hz,one_mul]
    exact BorelQuotient.quotientSLTorusEquiv_mk_torus F hF d
  rw [hc,he]
  have hul : u ∈ localGroup (F := F) i := by
    fin_cases i
    · exact hu.1
    · exact hu.2
  rw [(localGroup i).mul_mem_cancel_left hul]
  fin_cases i
  · change d.1 = 1 ↔ torusSL F d ∈ pointLocalSL F
    rw [mem_pointLocalSL_iff,torusSL_val]
    simp
  · change d.2 = 1 ↔ torusSL F d ∈ lineLocalSL F
    rw [mem_lineLocalSL_iff,torusSL_val]
    simp

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

private theorem cartan_borel {X : Subgroup G} (hX : IsCartan T L X) (x : X) :
    alignedQuotient D S m ⟨x,(hX.1 x.property).1⟩ ∈ borelSL S.field.Carrier := by
  have hn (i : Fin 2) := ((SL3.coordinates D S m).mem_normalizer_preimage_iff
    ((SL3.flag D S m).space i.castSucc) ⟨x,(hX.1 x.property).1⟩).mp
      (SL3.cartan_normalizes D S m hX i.castSucc x.property)
  have hh (i : Fin 2) : alignedQuotient D S m ⟨x,(hX.1 x.property).1⟩ ∈ parabolic i :=
    (aligned_stabilizer _ _ i).mp (hn i)
  exact ⟨hh 0,hh 1⟩

private def cartanProjection {X : Subgroup G} (hX : IsCartan T L X) :
    X →* borelSL S.field.Carrier :=
  ((alignedQuotient D S m).comp (inclusion (hX.1.trans inf_le_left))).codRestrict _
    (cartan_borel D S m hX)

private def characters {X : Subgroup G} (hX : IsCartan T L X) :
    X →* S.field.Carrierˣ × S.field.Carrierˣ :=
  (borelCharacters S.field.card_eq).comp (cartanProjection D S m hX)

private theorem characters_injective {X : Subgroup G} (hX : IsCartan T L X) :
    Function.Injective (characters D S m hX) := by
  have hk : IsPGroup 2 (cartanProjection D S m hX).ker := by
    rw [cartanProjection,MonoidHom.ker_codRestrict]
    change IsPGroup 2 ((alignedQuotient D S m).ker.comap
      (inclusion (hX.1.trans inf_le_left)))
    rw [alignedQuotient_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hc : IsPGroup 2 (characters D S m hX).ker := by
    change IsPGroup 2 ((borelCharacters S.field.card_eq).ker.comap (cartanProjection D S m hX))
    rw [borelCharacters_ker]
    exact pCore_isPGroup.comap_of_ker_isPGroup _ hk
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (card_eq_one.mp (hc.card_eq_or_dvd.resolve_right
      (hX.odd.of_dvd_nat (card_subgroup_dvd_card _)).not_two_dvd_nat))

private theorem characters_membership {X : Subgroup G} (hX : IsCartan T L X)
    (i : Fin 2) (x : X) :
    (if i = 0 then (characters D S m hX x).1 else (characters D S m hX x).2) = 1 ↔
      (x : G) ∈ (SL3.flag D S m).Li i := by
  rw [show characters D S m hX x = borelCharacters S.field.card_eq
    (cartanProjection D S m hX x) from rfl,borelCharacters_local]
  let R := ((SL3.flag D S m).Li i).subgroupOf L
  let U := X.subgroupOf L ⊓ (R.map (alignedQuotient D S m)).comap (alignedQuotient D S m)
  have ho : Odd (Nat.card U) := by
    apply Odd.of_dvd_nat _ (card_dvd_of_le (show U ≤ X.subgroupOf L from inf_le_left))
    rw [Nat.card_congr (subgroupOfEquivOfLe (hX.1.trans inf_le_left)).toEquiv]
    exact hX.odd
  have hp : IsPPerfect 2 U := by
    intro N hn htwo
    let := hn
    apply index_eq_one.mp
    change Nat.card (U ⧸ N) = 1
    exact htwo.card_eq_or_dvd.resolve_right (fun hd =>
      ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))
  have hn : (alignedQuotient D S m).ker ≤ normalizer (R : Set L) := by
    rw [alignedQuotient_ker,←subgroupOf_normalizer_eq
      (show (SL3.flag D S m).Li i ≤ L from (localResidual_le _).trans inf_le_left)]
    intro a ha
    exact core_normalizes_local D S m i (mem_map_of_mem L.subtype ha)
  have hUR : U ≤ R := le_of_isPPerfect_of_le_sup_of_normalizes U R _ hp
    (by rw [alignedQuotient_ker]; exact pCore_isPGroup) hn
    (by simpa only [U,comap_map_eq] using (inf_le_right : U ≤ _))
  constructor
  · intro hx
    change (⟨x,(hX.1 x.property).1⟩ : L) ∈ R
    apply hUR
    refine ⟨x.property,?_⟩
    change alignedQuotient D S m ⟨x,(hX.1 x.property).1⟩ ∈ R.map _
    rw [local_image]
    exact hx
  · intro hx
    have h := mem_map_of_mem (alignedQuotient D S m)
      (show (⟨x,(hX.1 x.property).1⟩ : L) ∈ R from hx)
    rw [local_image] at h
    exact h

/-- The two original linear residual intersections split the full Cartan. -/
theorem linear_cartan_split {X : Subgroup G} (hX : IsCartan T L X)
    (f : InvariantFlag (.sl3 m)) :
    (X ⊓ f.Li 0) ⊔ (X ⊓ f.Li 1) = X ∧ Disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1) := by
  have hc : Nat.card X = Nat.card (S.field.Carrierˣ × S.field.Carrierˣ) := by
    rw [(Coordinates.sl3 m).cartan_card hX,Nat.card_prod,Nat.card_units,S.field.card_eq,pow_two]
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (S.field.Carrierˣ × S.field.Carrierˣ)
  have hb : Function.Bijective (characters D S m hX) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨characters_injective D S m hX,by simpa only [Nat.card_eq_fintype_card] using hc⟩
  let e := MulEquiv.ofBijective (characters D S m hX) hb
  have hf (i : Fin 2) : f.Li i = (SL3.flag D S m).Li i := by
    change localResidual L ((Coordinates.sl3 m).preimage (f.space i.castSucc)) = _
    rw [SL3.flag_inner_unique D S m i.castSucc (f.space i.castSucc)
      (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
    rfl
  have h₀ (x : X) : (e x).1 = 1 ↔ (x : G) ∈ f.Li 0 := by
    rw [hf 0]
    exact characters_membership D S m hX 0 x
  have h₁ (x : X) : (e x).2 = 1 ↔ (x : G) ∈ f.Li 1 := by
    rw [hf 1]
    exact characters_membership D S m hX 1 x
  constructor
  · apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    let a := e.symm (1,(e ⟨x,hx⟩).2)
    let b := e.symm ((e ⟨x,hx⟩).1,1)
    have ha : (a : G) ∈ X ⊓ f.Li 0 := ⟨a.property,(h₀ a).mp (by simp [a])⟩
    have hb : (b : G) ∈ X ⊓ f.Li 1 := ⟨b.property,(h₁ b).mp (by simp [b])⟩
    have hab : (a : G) * b = x := by
      change ((a*b : X) : G) = x
      have he : a*b = ⟨x,hx⟩ := e.injective (by simp [a,b])
      exact congrArg Subtype.val he
    rw [←hab]
    exact mul_mem_sup ha hb
  · apply disjoint_def.mpr
    intro x hx hy
    have he : e ⟨x,hx.1⟩ = 1 := Prod.ext ((h₀ _).mpr hx.2) ((h₁ _).mpr hy.2)
    exact congrArg Subtype.val (e.map_eq_one_iff.mp he)


private theorem linear_inner_unique (f : InvariantFlag (.sl3 m)) : f.IsInnerUnique := by
  intro i U hU hT
  have he := SL3.flag_inner_unique D S m i U hU hT
  have hf := SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
    (inf_le_left.trans (f.invariant i))
  exact he.trans hf.symm

private theorem linear_local_model (f : InvariantFlag (.sl3 m)) (i : Fin 2) :
    ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2^S.field.degree) :=
  ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
    ⟨SL3.flagLocalCoreEquiv S m f i⟩⟩

/-- In the original linear branch the Cartan belongs to the literal third
vertex, using its two original residual intersections. No common Q is needed. -/
theorem linear_triangle_cartan_le_join
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    X ≤ K₀ ⊔ f.Li 1 := by
  obtain ⟨_,h₁,h₀⟩ := first_triangle_cartan_intersections D S f
    (linear_inner_unique D S m f) (linear_local_model D S m f 0) hd
    hX hK hLK hK₀ hK₀K hk hp
  rw [←(linear_cartan_split D S m hX f).1]
  exact sup_le_sup ((h₁.symm.trans h₀).le.trans inf_le_right) inf_le_right

/-- Neither of the two residuals contains the full Cartan; both are proper
in the original join. This step is independent of common-normal existence. -/
theorem linear_triangle_proper_residuals
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    K₀ < K₀ ⊔ f.Li 1 ∧ f.Li 1 < K₀ ⊔ f.Li 1 ∧
      ¬ X ≤ K₀ ∧ ¬ X ≤ f.Li 1 := by
  obtain ⟨hc,h₁,h₀⟩ := first_triangle_cartan_intersections D S f
    (linear_inner_unique D S m f) (linear_local_model D S m f 0) hd
    hX hK hLK hK₀ hK₀K hk hp
  have hXI := linear_triangle_cartan_le_join D S m f hd hX hK hLK hK₀ hK₀K hk hp
  have hn₀ : ¬ X ≤ K₀ := by
    intro h
    have he : X ⊓ K = X := h₀.trans (inf_eq_left.mpr h)
    rw [he,(Coordinates.sl3 m).cartan_card hX,hd] at hc
    norm_num at hc
  have hn₂ : ¬ X ≤ f.Li 1 := by
    intro h
    have hdis := (linear_cartan_split D S m hX f).2
    rw [inf_eq_left.mpr h] at hdis
    have he : X ⊓ f.Li 0 = ⊥ := disjoint_self.mp
      (Disjoint.mono_right (inf_le_left : X ⊓ f.Li 0 ≤ X) hdis)
    rw [h₁,he,card_bot] at hc
    contradiction
  exact ⟨lt_of_le_of_ne le_sup_left (fun he => hn₀ (he.symm ▸ hXI)),
    lt_of_le_of_ne le_sup_right (fun he => hn₂ (he.symm ▸ hXI)),hn₀,hn₂⟩

/-- Both original local joins have GL₂(4) quotients with their smaller
residual two-cores unchanged. The markings use the same Cartan as the linear flag. -/
theorem linear_triangle_local_gl_markings
    (f : InvariantFlag (.sl3 m))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    X ≤ normalizer (K₀ : Set G) ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      (K₀ ⊔ X : Subgroup G).pCoreIn 2 = K₀.pCoreIn 2 ∧
      IsGLTwoFour ((K₀ ⊔ X : Subgroup G) ⧸ pCore 2 (K₀ ⊔ X : Subgroup G)) ∧
      (f.Li 1 ⊔ X : Subgroup G).pCoreIn 2 = (f.Li 1).pCoreIn 2 ∧
      IsGLTwoFour ((f.Li 1 ⊔ X : Subgroup G) ⧸ pCore 2 (f.Li 1 ⊔ X : Subgroup G)) := by
  have hu := linear_inner_unique D S m f
  have hm₁ := linear_local_model D S m f 0
  have hm₂ := linear_local_model D S m f 1
  have hXN (i : Fin 2) : X ≤ normalizer (f.Li i : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi i.castSucc : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX i.castSucc)
    exact (hx.trans (L ⊓ normalizer (f.Vi i.castSucc : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXP : X ≤ normalizer (((T : Subgroup G) ⊓ f.Li 0 : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ f.Li 0 = ((T : Subgroup G) ⊓ L) ⊓ f.Li 0 := by
      exact le_antisymm
        (le_inf (le_inf inf_le_left (inf_le_right.trans ((localResidual_le _).trans inf_le_left))) inf_le_right)
        (inf_le_inf inf_le_left le_rfl)
    rw [he]
    exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) (hXN 0)).trans
      inf_normalizer_le_normalizer_inf
  have hNK : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  obtain ⟨hn₀,hm₀⟩ := other_local_marking_of_normalizes_intersection T ht
    ((f.invariant 0).trans hNK) (flag_mem_local_of_model D S f 0 hm₁).1 hLK hK₀.1 hK₀K
    ((f.cartan_normalizes hu hX 0).trans hNK) (hXN 0) hXP hk
  obtain ⟨hc,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hcardX : Nat.card X = 9 := by
    rw [(Coordinates.sl3 m).cartan_card hX,hfour]
    norm_num
  have hcard₀ : Nat.card (X ⊓ K₀ : Subgroup G) = 3 := h₀ ▸ hc
  have hcard₁ : Nat.card (X ⊓ f.Li 0 : Subgroup G) = 3 := h₁ ▸ hc
  have hcard₂ : Nat.card (X ⊓ f.Li 1 : Subgroup G) = 3 := by
    obtain ⟨hgen,hdis⟩ := linear_cartan_split D S m hX f
    let e := (Coordinates.sl3 m).cartanTorusEquiv hX
    let : CommGroup X := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
    have hcomm : X ⊓ f.Li 1 ≤ centralizer (X ⊓ f.Li 0 : Set G) := by
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm (⟨y,hy.1⟩ : X) (⟨x,hx.1⟩ : X))
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1)
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hdis
    rw [hgen,hcardX,hcard₁] at hh
    omega
  obtain ⟨hc₀,hg₀⟩ := residual_cartan_gl_two_four K₀ X hn₀ hm₀ hcardX hcard₀
  obtain ⟨hc₂,hg₂⟩ := residual_cartan_gl_two_four (f.Li 1) X (hXN 1)
    (by simpa [hfour] using hm₂) hcardX hcard₂
  exact ⟨hn₀,hm₀,hc₀,(isGLTwoFour_iff _).mpr hg₀,hc₂,(isGLTwoFour_iff _).mpr hg₂⟩


/-- The linear common-Q construction now supplies Cartan containment, both
three-ranks, both proper marked locals, and the SL₃(4) third-vertex exclusion.
There is no extra Cartan-placement premise. Existence of Q and exclusion of
the original linear vertex remain with the source assembly owner. -/
theorem linear_triangle_geometry_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    Source.NormalComponentIn (I ⊔ (T : Subgroup G)) I ∧
      I ∈ Chapter1.L G T ∧ I ∈ Chapter1.He G ∧ X ≤ I ∧
      primeRank 3 I = 2 ∧ primeRank 3 (I ⧸ pCore 2 I) = 2 ∧
      ¬ Source.IsSL (I ⧸ pCore 2 I) 3 4 ∧
      ∀ B : Subgroup G, B = K₀ ∨ B = f.Li 1 →
        B < I ∧ B ⊔ X ≤ I ∧ X ≤ normalizer (B : Set G) ∧
        ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 ∧
        (B ⊔ X : Subgroup G).pCoreIn 2 = B.pCoreIn 2 ∧
        IsGLTwoFour ((B ⊔ X : Subgroup G) ⧸ pCore 2 (B ⊔ X : Subgroup G)) := by
  intro I
  have hu := linear_inner_unique D S m f
  have hm (i : Fin 2) := linear_local_model D S m f i
  obtain ⟨hI,hIL,hIH,_,_⟩ := triangle_join_component_of_common_normal_projective
    D S f hu (hm 0) (hm 1) hd hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hXI := linear_triangle_cartan_le_join D S m f hd hX hK hLK hK₀ hK₀K hk hp
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hn : I ≤ normalizer (Q : Set G) := sup_le hKQ hLQ
  have hupp := (_root_.primeRank_le_of_injective 3 (inclusion hn)
    (inclusion_injective hn)).trans (hN.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hlo := _root_.primeRank_le_of_injective 3 (inclusion hXI) (inclusion_injective hXI)
  rw [(Coordinates.sl3 m).cartan_primeRank hX Nat.prime_three (by simp [hd])] at hlo
  have hr := le_antisymm hupp hlo
  have hrq := (primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr
  have hnot := linear_triangle_join_not_sl3 D S m hd f hX hK hLK hgen hTK₀ hIL.1 hXI hcard
  obtain ⟨hn₀,hm₀,hc₀,hg₀,hc₂,hg₂⟩ := linear_triangle_local_gl_markings
    D S m f hd hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hlt₀,hlt₂,_,_⟩ := linear_triangle_proper_residuals
    D S m f hd hX hK hLK hK₀ hK₀K hk hp
  refine ⟨hI,hIL,hIH,hXI,hr,hrq,hnot,?_⟩
  intro B hB
  rcases hB with rfl | rfl
  · exact ⟨hlt₀,sup_le le_sup_left hXI,hn₀,hm₀,hc₀,hg₀⟩
  · have hn₂ : X ≤ normalizer (f.Li 1 : Set G) := by
      have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
        le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
      exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
    exact ⟨hlt₂,sup_le le_sup_right hXI,hn₂,by simpa [hd] using hm 1,hc₂,hg₂⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
