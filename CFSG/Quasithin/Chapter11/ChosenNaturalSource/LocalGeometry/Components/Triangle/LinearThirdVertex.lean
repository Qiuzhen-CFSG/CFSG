module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstPrimeLinear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import Theory.SpecificGroups.PSL3.LinearThreeCubicCartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.LinearCartanExclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.CartanIntersection
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients


/-!
# The common cubic and the linear third-vertex exclusion

For the original natural SL₃(4) flag, a cubic centralizing either local
PSL₂ quotient has scalar image in the full SL₃ quotient. Transport the
point and line calculations through the same aligned quotient, retaining
the smaller residual two-cores. Thus the two actual Cartan kernels X₁
and X₂ coincide with the Cartan kernel on L/O₂(L).

The existing O²(X₁T) normalizer argument shows that this common cubic
cannot centralize the strict containing component K/O₂(K). More generally,
the proved local A₅ placement in SL₃(4) makes a cubic centralizing that
local section centralize the entire SL₃ quotient. Apply this to the
literal I = K₀ ∨ L₂: if I/O₂(I) were SL₃(4), the common cubic would force
I ≤ N_G(L), hence K ≤ N_G(L), contradicting L₁ < K. This does not require
a natural marking or maximal-faithful membership on I.

The final common-Q consumer constructs relative-component and He
membership from the original Q and retains the preceding Cartan placement
X ≤ I. That placement in the original linear branch and existence of Q
still require proof. Excluding the original L/O₂(L) = SL₃(4), the Weyl
normalizer escape, the subsequent module comparison, both final triangle
orientations and full 11.1.1--3 assembly remain with
qt-d-1222-natural-relative-components. Original flag/Cartan inputs and
final earlier-source discharge retain qt-d-1222-natural-local-geometry.
No assertion of B.4.14 or choice of its projective module extension is used.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 11.1.2,
printed p.763, the equality X₁ = X₂ and exclusion of the SL₃(4) third
vertex, using the earlier normalizer argument on p.762. The native local
placement is the checked Chapter A input also used in source 9.3.8.
-/

open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
open SL3.PlaneAction ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

omit [Finite G] in
private theorem core_kernel_of_commutators {B : Subgroup G} {x : G}
    (hn : x ∈ normalizer (B : Set G))
    (hc : ∀ b ∈ B, ⁅x,b⁆ ∈ B.pCoreIn 2) :
    x ∈ Closure.coreQuotientCentralizer B := by
  refine ⟨⟨x,hn⟩,MonoidHom.mem_ker.mpr ?_,rfl⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
  rw [Closure.coreQuotientAction_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  obtain ⟨r,hr,he⟩ := hc b b.property
  have he' : r = B.normalizerMonoidHom ⟨x,hn⟩ b / b := by
    apply Subtype.ext
    simpa only [subtype_apply,div_eq_mul_inv,coe_mul,coe_inv,
      normalizerMonoidHom_apply_apply_coe,commutatorElement_def] using he
  exact he' ▸ hr

private theorem cubic_local_central (hd : S.field.degree = 2) (i : Fin 2)
    (x : L) (hx : (x : G) ∈ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li i))
    (hx3 : x^3 = 1) :
    alignedQuotient D S m x ∈ center (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier) := by
  let B := (SL3.flag D S m).Li i
  let q := alignedQuotient D S m
  let p := localProjection D S m i
  have hcore := p.comap_pCore_of_ker_isPGroup
    (localProjection_surjective D S m i) (localProjection_ker_isTwoGroup D S m i)
  have hc : ⁅zpowers (q x),localGroup (F := S.field.Carrier) i⁆ ≤
      (localGroup (F := S.field.Carrier) i).pCoreIn 2 := by
    apply commutator_le.mpr
    intro y hy b hb
    obtain ⟨n,rfl⟩ := hy
    obtain ⟨a,ha⟩ := localProjection_surjective D S m i ⟨b,hb⟩
    have ha' : q ⟨a,(localResidual_le _ a.property).1⟩ = b :=
      (localProjection_coe D S m i a).symm.trans (congrArg Subtype.val ha)
    obtain ⟨r,hr,he⟩ := Closure.coreQuotientCentralizer_commutator
      ((Closure.coreQuotientCentralizer B).zpow_mem hx n) a.property
    have hrp : p r ∈ pCore 2 (localGroup (F := S.field.Carrier) i) := by
      change r ∈ (pCore 2 (localGroup (F := S.field.Carrier) i)).comap p
      rw [hcore]
      exact hr
    refine ⟨p r,hrp,?_⟩
    change (localProjection D S m i r : Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier) = _
    rw [localProjection_coe]
    have hre : (⟨r,(localResidual_le _ r.property).1⟩ : L) =
        ⁅x^n,⟨a,(localResidual_le _ a.property).1⟩⁆ := Subtype.ext he
    rw [hre,map_commutatorElement,map_zpow,ha']
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hq3 : q x ^ 3 = 1 := by rw [←map_pow,hx3,map_one]
  fin_cases i
  · exact Matrix.PSL3.LinearThree.cubic_point_section_central hF (q x) hc hq3
  · exact Matrix.PSL3.LinearThree.cubic_line_section_central hF (q x) hc hq3


include m in
private theorem cartan_cube (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) (x : X) : x^3 = 1 := by
  let e := (Coordinates.sl3 m).cartanTorusEquiv hX
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hunit : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,hF]
  have hp (u : S.field.Carrierˣ) : u^3 = 1 := by
    rw [←hunit]
    exact pow_card_eq_one'
  apply e.injective
  rw [map_pow,map_one]
  exact Prod.ext (hp _) (hp _)

private theorem aligned_central_iff (x : L) :
    alignedQuotient D S m x ∈ center (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier) ↔
      (x : G) ∈ Closure.coreQuotientCentralizer L := by
  let q := alignedQuotient D S m
  constructor
  · intro hz
    apply core_kernel_of_commutators (L.le_normalizer x.property)
    intro l hl
    let l' : L := ⟨l,hl⟩
    have hq : q ⁅x,l'⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp hz (q l')).symm
    have hk : ⁅x,l'⁆ ∈ pCore 2 L := by
      rw [←alignedQuotient_ker D S m]
      exact hq
    exact ⟨⁅x,l'⁆,hk,rfl⟩
  · intro hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l,rfl⟩ := alignedQuotient_surjective D S m y
    obtain ⟨r,hr,he⟩ := Closure.coreQuotientCentralizer_commutator hx l.property
    have hre : r = ⁅x,l⁆ := Subtype.ext he
    have hh : q ⁅x,l⁆ = 1 := by
      rw [←hre]
      change r ∈ (alignedQuotient D S m).ker
      rw [alignedQuotient_ker]
      exact hr
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hh
    exact hh.symm

/-- In the original SL₃(4) natural marking, the Cartan kernel on either
parabolic quotient is exactly its kernel on the whole component quotient. -/
theorem linear_four_cartan_section_kernel
    (hd : S.field.degree = 2) (f : InvariantFlag (.sl3 m))
    {X : Subgroup G} (hX : IsCartan T L X) (i : Fin 2) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li i) =
      X ⊓ Closure.coreQuotientCentralizer L := by
  have he : f.Li i = (SL3.flag D S m).Li i := by
    change localResidual L ((Coordinates.sl3 m).preimage (f.space i.castSucc)) = _
    rw [SL3.flag_inner_unique D S m i.castSucc (f.space i.castSucc)
      (f.dimension i.castSucc) (inf_le_left.trans (f.invariant i.castSucc))]
    rfl
  have hxA : X ≤ normalizer (f.Li i : Set G) := by
    have hu : f.IsInnerUnique := by
      intro j U hU hT
      have he' := SL3.flag_inner_unique D S m j U hU hT
      have hf := SL3.flag_inner_unique D S m j (f.space j) (f.dimension j)
        (inf_le_left.trans (f.invariant j))
      exact he'.trans hf.symm
    exact ((le_inf ((hX.1.trans inf_le_left).trans L.le_normalizer)
      ((f.cartan_normalizes hu hX i.castSucc).trans (normalizer _).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    have hxL : x ∈ L := (hX.1 hx).1
    have hp : (⟨x,hxL⟩ : L)^3 = 1 :=
      Subtype.ext (congrArg (fun y : X => (y : G)) (cartan_cube D S m hd hX ⟨x,hx⟩))
    exact ⟨hx,(aligned_central_iff D S m ⟨x,hxL⟩).mp
      (cubic_local_central D S m hd i ⟨x,hxL⟩ (he ▸ hc) hp)⟩
  · rintro x ⟨hx,hc⟩
    refine ⟨hx,core_kernel_of_commutators (hxA hx) ?_⟩
    intro a ha
    exact inf_pCoreIn_le_of_le 2 ((localResidual_le _).trans inf_le_left)
      ⟨le_normalizer_iff_commutator_le_right.mp (show zpowers x ≤ normalizer (f.Li i : Set G)
        from zpowers_le.mpr (hxA hx)) (commutator_mem_commutator (mem_zpowers x) ha),
      Closure.coreQuotientCentralizer_commutator hc ((localResidual_le _ ha).1)⟩

/-- The equality X₁ = X₂ at the start of the linear triangle exclusion,
with both kernels defined by their original residual quotients. -/
theorem linear_four_cartan_kernels_eq
    (hd : S.field.degree = 2) (f : InvariantFlag (.sl3 m))
    {X : Subgroup G} (hX : IsCartan T L X) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li 0) =
      X ⊓ Closure.coreQuotientCentralizer (f.Li 1) := by
  rw [linear_four_cartan_section_kernel D S m hd f hX 0,
    linear_four_cartan_section_kernel D S m hd f hX 1]

/-- The original strict containing component cannot centralize the common
cubic quotient actor. Otherwise the actual O²(X₁T) normalizer argument
places K in N_G(L) and forces K = L₁. -/
theorem linear_four_strict_component_cubic
    (hd : S.field.degree = 2) (f : InvariantFlag (.sl3 m))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    X ⊓ Closure.coreQuotientCentralizer (f.Li 0) =
      X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ∧
      ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ Closure.coreQuotientCentralizer K := by
  have he := linear_four_cartan_kernels_eq D S m hd f hX
  refine ⟨he,?_⟩
  intro hcK
  let A := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  have hne : A ≠ ⊥ := by
    intro hz
    change Nat.card A = 3 at hcard
    rw [hz,Nat.card_unique] at hcard
    contradiction
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 0⟩⟩
  apply hLK.ne
  apply flag_component_eq_of_common_quotient_kernel D S f 0 hm hK hLK.le
    (inf_le_left.trans (hX.1.trans inf_le_left))
    (hX.odd.of_dvd_nat (card_dvd_of_le (show A ≤ X from inf_le_left))) hne
  · exact (linear_four_cartan_section_kernel D S m hd f hX 0).le.trans inf_le_right
  · exact he.le.trans hcK


omit [Finite G] in
private theorem kernel_eq_sectionCentralizer (B : Subgroup G) :
    Closure.coreQuotientCentralizer B = Chapter4.sectionCentralizer B := by
  apply le_antisymm
  · apply (Chapter4.le_sectionCentralizer_iff _ B).mpr
    exact ⟨map_subtype_le _,commutator_le.mpr fun _ hx _ hb =>
      Closure.coreQuotientCentralizer_commutator hx hb⟩
  · have hc := (Chapter4.le_sectionCentralizer_iff (Chapter4.sectionCentralizer B) B).mp le_rfl
    intro x hx
    exact core_kernel_of_commutators (hc.1 hx) (fun b hb =>
      hc.2 (commutator_mem_commutator hx hb))

/-- A cubic subgroup in an actual SL₃(4) quotient that centralizes a proper
local A₅ section centralizes the entire quotient. The local section is
placed by the proved special-linear embedding theorem. -/
theorem linear_four_local_cubic_kernel
    {I B E : Subgroup G} (hB : B ∈ localCComponents T)
    (hI : I ∈ localCComponents T) (hBI : B < I)
    (hEI : E ≤ I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmI : Source.IsSL (I ⧸ pCore 2 I) 3 4)
    (hEB : E ≤ Closure.coreQuotientCentralizer B)
    (h3 : ∀ x ∈ E, x^3 = 1) : E ≤ Closure.coreQuotientCentralizer I := by
  obtain ⟨P,hP,hBP⟩ := ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_in_local_overgroup
    T hB hI hBI.le
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmI
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by simpa using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using
      hI.subgroupOf_of_le (show I ≤ I from le_rfl) (show I ≤ I ⊔ T from le_sup_left)
  have hproper : (B.subgroupOf I).map q ≠ ⊤ := by
    intro he
    have he' : (B.subgroupOf I).map q = (⊤ : Subgroup I).map q := by
      rw [he,map_top_of_surjective q hq]
    have ht := local_cComponent_eq_of_map_eq hBP htop le_top q
      (hk.le_sylow_of_normal P) he'
    exact hBI.not_ge (subgroupOf_eq_top.mp ht)
  have hker (A : Subgroup I) : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨F',_,_,hF',⟨eB⟩⟩ := hmB
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF'
  rw [kernel_eq_sectionCentralizer] at hEB ⊢
  exact Chapter10.source_tensor_linear_original_chosen_factor hF I B I E hBI.le le_rfl hEI
    q (P.mapSurjective hq)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hBP q) hproper (eB.trans a)
    (hker _) hEB (hEI.trans I.le_normalizer) (hker _) h3

/-- In the source's original SL₃(4) branch, the actual third vertex
I = K₀ ∨ L₂ cannot also have SL₃(4) quotient. The input X ≤ I and local
membership are the preceding common-normal/Cartan construction on p.763;
no natural action or maximal-faithful membership on I is assumed. -/
theorem linear_triangle_join_not_sl3
    (hd : S.field.degree = 2) (f : InvariantFlag (.sl3 m))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hgen : f.Li 0 ⊔ K₀ = K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hI : (K₀ ⊔ f.Li 1) ∈ localCComponents T)
    (hXI : X ≤ K₀ ⊔ f.Li 1)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3) :
    ¬ Source.IsSL ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4 := by
  intro hmI
  let I := K₀ ⊔ f.Li 1
  let A := X ⊓ Closure.coreQuotientCentralizer (f.Li 1)
  have hm (i : Fin 2) : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f i⟩⟩
  have hKnot : ¬ K ≤ normalizer (L : Set G) := fun h => hLK.ne
    (flag_component_eq_of_le_component_normalizer D S f 0 (hm 0) hK.1 hLK.le h)
  have hproper : f.Li 1 < I := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro he
    have hK₀L : K₀ ≤ L :=
      (show K₀ ≤ I from le_sup_left).trans (he ▸ (localResidual_le _).trans inf_le_left)
    apply hKnot
    rw [←hgen]
    exact (sup_le ((localResidual_le _).trans inf_le_left) hK₀L).trans L.le_normalizer
  have hthree : ∀ x ∈ A, x^3 = 1 := fun x hx =>
    congrArg (fun y : X => (y : G)) (cartan_cube D S m hd hX ⟨x,hx.1⟩)
  have hAI : A ≤ Closure.coreQuotientCentralizer I :=
    linear_four_local_cubic_kernel (flag_mem_local_of_model D S f 1 (hm 1)).1 hI hproper
      (inf_le_left.trans hXI) (by simpa [hd] using hm 1) hmI inf_le_right hthree
  have hAL : A ≤ Closure.coreQuotientCentralizer L :=
    (linear_four_cartan_section_kernel D S m hd f hX 1).le.trans inf_le_right
  have hne : A ≠ ⊥ := by
    intro hz
    change Nat.card A = 3 at hcard
    rw [hz,Nat.card_unique] at hcard
    contradiction
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    (le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1))
  have hIM := component_le_normalizer_of_common_quotient_kernel D S hTI
    (inf_le_left.trans (hX.1.trans inf_le_left))
    (hX.odd.of_dvd_nat (card_dvd_of_le (show A ≤ X from inf_le_left))) hne hAL hAI
  apply hKnot
  rw [←hgen]
  exact sup_le (((localResidual_le _).trans inf_le_left).trans L.le_normalizer)
    (le_sup_left.trans hIM)


/-- Apply the exclusion to the literal common-Q join of the original linear
flag. Local membership is constructed from Q. The original Cartan placement
X ≤ I is retained as the preceding p.763 premise; Q existence and that
placement in the linear branch remain with the source assembly owner. -/
theorem linear_triangle_join_not_sl3_of_common_normal
    (hd : S.field.degree = 2) (f : InvariantFlag (.sl3 m)) (hu : f.IsInnerUnique)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hXI : X ≤ K₀ ⊔ f.Li 1)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      ¬ Source.IsSL ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4 := by
  have hm (i : Fin 2) : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f i⟩⟩
  obtain ⟨hrelative,hlocal,hHe,_,_⟩ := triangle_join_component_of_common_normal_projective
    D S f hu (hm 0) (hm 1) hd hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  exact ⟨hrelative,hHe,linear_triangle_join_not_sl3 D S m hd f hX hK hLK hgen hTK₀
    hlocal.1 hXI hcard⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
