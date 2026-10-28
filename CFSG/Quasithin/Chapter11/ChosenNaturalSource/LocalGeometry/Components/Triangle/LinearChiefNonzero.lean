module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearChiefNatural
public import Theory.Representation.SL2NaturalCommonQuotient.Constituents

/-!
# A nonzero marked natural quotient on the selected chief section

The original inner cubic X_K lies in L⁺: its original Sylow placement puts
it in L₁, and the cubic normalizer modulo its solvable residual is a
two-group. The surviving X_K commutator on the SAME selected section
therefore rules out the trivial branch of its natural-quotient dichotomy.

We obtain an equivariant epimorphism C_W(X₁) -> F₄² through the original
point SL₂ marking. Its kernel is exactly C_W(X₁) intersect C_W(L⁺), of
index sixteen. The original fixed representatives map onto the entire
star image, and the epimorphism preserves both original projections.
Every irreducible noncentral quotient of an invariant subgroup of C_W(X₁)
is identified through this same map with the same natural plane.

Both chief-section endpoints, the faithful irreducible KX/O₂(KX) action,
and the surviving original commutator remain in the conclusion. No positive
multiplicity of an ambient natural or dual layer is assumed. The comparison
of all L⁺ constituents on W, projective extension selection, the other
centralizer branch, common-normal existence and both triangle orientations
still require proof. This is not the full source 11.1.2.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764. The local odd-residual argument adapts the
already checked proof in LinearCubicMovement.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
open NoncentralChiefRefinement

private theorem odd_le_residual {A B : Type*} [Group A] [Finite A] [Group B]
    [Group.IsPerfect B] (q : A →* B) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (Y : Subgroup A) (ho : Odd (Nat.card Y)) :
    Y ≤ solvableResidual A := by
  rw [←pResidual_eq_solvableResidual_of_perfect_image q hq hk]
  apply le_pResidual_of_isPPerfect
  intro N hn hp
  let := hn
  apply index_eq_one.mp
  change Nat.card (Y ⧸ N) = 1
  exact hp.card_eq_or_dvd.resolve_right
    (fun hd => ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))

/-- Odd elements of the original point residual that belong to the Cartan
lie in the actual cubic normalizer residual, not just its two-core quotient. -/
theorem linear_point_cartan_intersection_le_plus
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li 0) : Subgroup G) = 3) :
    X ⊓ (SL3.flag D S m).Li 0 ≤
      localResidual ((SL3.flag D S m).Li 0)
        (X ⊓ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li 0)) := by
  let f := SL3.flag D S m
  let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  let H := localResidual (f.Li 0) E
  let N := f.Li 0 ⊓ normalizer (E : Set G)
  let _ : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  let _ : IsMulCommutative X := .of_comm fun a b =>
    ((Coordinates.sl3 m).cartanTorusEquiv hX).injective (by simp only [map_mul,mul_comm])
  have hYN : X ⊓ f.Li 0 ≤ N := le_inf inf_le_right
    (inf_le_left.trans ((X.le_centralizer.trans (centralizer_le (show E ≤ X from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)))
  let q := (QuotientGroup.mk' (pCore 2 (f.Li 0))).comp
    (inclusion (show N ≤ f.Li 0 from inf_le_left))
  obtain ⟨_,_,_,e,he⟩ := linear_point_cubic_residual_cover D S m f hcard
  have hs : Function.Surjective q := by
    intro w
    obtain ⟨v,hv⟩ := e.surjective w
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) v
    exact ⟨⟨h,localResidual_le E h.property⟩,(he h).symm.trans hv⟩
  have hk : IsPGroup 2 q.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have ho : Odd (Nat.card ((X ⊓ f.Li 0).subgroupOf N)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYN).toEquiv]
    exact hX.odd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hr := odd_le_residual q hs hk ((X ⊓ f.Li 0).subgroupOf N) ho
  intro x hx
  exact mem_map_of_mem N.subtype (hr (show (⟨x,hYN hx⟩ : N) ∈ (X ⊓ f.Li 0).subgroupOf N from hx))

/-- The original inner cubic belongs to L-plus. The point-component
intersection is recovered from the original Sylow placement. -/
theorem linear_point_inner_cubic_le_plus
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((SL3.flag D S m).Vi 0 : Set G)) K)
    (hLK : (SL3.flag D S m).Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li 0) : Subgroup G) = 3) :
    X ⊓ K ≤ localResidual ((SL3.flag D S m).Li 0)
      (X ⊓ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li 0)) := by
  let f := SL3.flag D S m
  have hu : f.IsInnerUnique := by
    intro i W hW hT
    exact (SL3.flag_inner_unique D S m i W hW hT).trans
      (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 0⟩⟩
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hXN : X ≤ normalizer (f.Li 0 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 0 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 0)
    exact (hx.trans (L ⊓ normalizer (f.Vi 0 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXi : X ≤ normalizer (((T : Subgroup G) ⊓ f.Li 0 : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ f.Li 0 = ((T : Subgroup G) ⊓ L) ⊓ f.Li 0 :=
      le_antisymm
        (le_inf (le_inf inf_le_left (inf_le_right.trans ((localResidual_le _).trans inf_le_left))) inf_le_right)
        (inf_le_inf inf_le_left le_rfl)
    rw [he]
    exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) hXN).trans
      inf_normalizer_le_normalizer_inf
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  have hlocal := (flag_mem_local_of_model D S f 0 hm).1
  have hinner := odd_intersection_le_local T htop hTK hlocal hLK hlocal hLK
    (inf_le_right : X ⊓ K ≤ K) (hX.odd.of_dvd_nat (card_dvd_of_le inf_le_left))
    (inf_le_left.trans hXi) hk
  exact (le_inf inf_le_left hinner).trans (linear_point_cartan_intersection_le_plus D S m hX hcard)


/-- A surviving original inner-cubic commutator prevents the fixed kernel
from being the whole cubic-fixed section. Both section endpoints are fixed. -/
theorem linear_point_fixed_kernel_ne_top
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((SL3.flag D S m).Vi 0 : Set G)) K)
    (hLK : (SL3.flag D S m).Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((SL3.flag D S m).Li 0) : Subgroup G) = 3) :
    let f := SL3.flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (B A : NormalNode J) (a : A.val),
      ((a : J) : G) ∈ centralizer (E : Set G) →
      ∀ z : (X ⊓ K : Subgroup G),
        ⁅inclusion (show X ⊓ K ≤ J from inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val →
        (sectionFixed B A (H.subgroupOf J)).subgroupOf (sectionFixed B A (E.subgroupOf J)) ≠ ⊤ := by
  intro f E H U J B A a ha z hz htop
  let q := QuotientGroup.mk' (B.val.subgroupOf A.val)
  have hw : q a ∈ sectionFixed B A (E.subgroupOf J) := by
    intro e
    rw [sectionAction_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    change (e.val : G) * (a.val : G) * (e.val : G)⁻¹ = (a.val : G)
    rw [ha e.val e.property,mul_inv_cancel_right]
  have hh : q a ∈ sectionFixed B A (H.subgroupOf J) :=
    htop.ge (show (⟨q a,hw⟩ : sectionFixed B A (E.subgroupOf J)) ∈ ⊤ from mem_top _)
  have hinner := linear_point_inner_cubic_le_plus D S m hX hK hLK hk hcard
  let j : J := inclusion (show X ⊓ K ≤ J from
    inf_le_left.trans (le_sup_right.trans le_sup_left)) z
  have he := hh ⟨j,hinner z.property⟩
  rw [sectionAction_mk] at he
  have hb := QuotientGroup.eq_iff_div_mem.mp he
  apply hz
  change j * (a : J) * j⁻¹ / (a : J) ∈ B.val at hb
  simpa only [commutatorElement_def,div_eq_mul_inv] using hb

open SL3 SL3.PlaneAction ChapterG.Section02.LinearThree Matrix.PSL3.LinearThree

/-- Fixed-section comparison before selecting the faithful chief interval. -/
private theorem section_natural_epimorphism
    (hd : S.field.degree = 2)
    (hfix : (flag D S m).Li 0 ≤ centralizer ((flag D S m).Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((flag D S m).Vi 0 : Set G)) K)
    (hLK : (flag D S m).Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) ≤
      centralizer ((flag D S m).Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let f := flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∀ (B A : NormalNode J) (_hBA : B ≤ A) (hAU : A.val ≤ U.subgroupOf J)
      (he : IsElementaryAbelian 2 (Section B A)), let _ := he
      let _ : CommGroup (Section B A) :=
        { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
      Function.Surjective (fixedProjection B A (E.subgroupOf J)) →
      (∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
        ∃ z : (X ⊓ K : Subgroup G),
          ⁅inclusion (show X ⊓ K ≤ J from inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val) →
      (let C := sectionFixed B A (E.subgroupOf J)
         let R := (sectionFixed B A (H.subgroupOf J)).subgroupOf C
         let q := fixedProjection B A (E.subgroupOf J)
         let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
           (hLK.le.trans (le_sup_left.trans le_sup_left))
         let r := (pointConstituentProjection D S m).comp
           (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left))
         Function.Surjective q ∧ R.index = 16 ∧
         ∃ eStar : (linearPointSetup D S m f).star U ≃* Multiplicative (Fin 2 → S.field.Carrier),
         ∃ π : C →* Multiplicative (Fin 2 → S.field.Carrier),
           Function.Surjective π ∧ π.ker = R ∧
           (∀ a, π (q a) = eStar (pointFixedStarImage D S m A hAU a)) ∧
           (∀ (h : H) (u v : C),
             (v : Section B A) = sectionAction B A (inclusion hHJ h) u.val →
             π v = Matrix.SL2.naturalAction S.field.Carrier (r h) (π u)) ∧
           Function.Surjective (pointFixedStarImage D S m A hAU) ∧
           ∀ (P : Subgroup C),
             (∀ (h : H) (x : P), ∃ y : P,
               (y.val : Section B A) = sectionAction B A (inclusion hHJ h) x.val.val) →
             ∀ (W : Type*) [CommGroup W] (τ : H →* MulAut W) (t : P →* W),
               Function.Surjective t →
               (∀ (h : H) (x y : P),
                 (y.val : Section B A) = sectionAction B A (inclusion hHJ h) x.val.val →
                 t y = τ h (t x)) →
               (∀ N : Subgroup W, (∀ h w, w ∈ N → τ h w ∈ N) → N = ⊥ ∨ N = ⊤) →
               (∃ h w, τ h w ≠ w) →
               ∃ e : W ≃* Multiplicative (Fin 2 → S.field.Carrier),
                 (∀ x : P, e (t x) = π x.val) ∧
                 ∀ h w, e (τ h w) = Matrix.SL2.naturalAction S.field.Carrier (r h) (e w)) := by
  intro f E H U J B A hBA hAU he
  let _ := he
  let _ : CommGroup (Section B A) :=
    { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
  intro _ _ hqs hsurv
  let C := sectionFixed B A (E.subgroupOf J)
  let R := (sectionFixed B A (H.subgroupOf J)).subgroupOf C
  let q := fixedProjection B A (E.subgroupOf J)
  let Z := QuotientGroup.CommonImage.kernelImage (pointFixedStarProjection D S m f A hAU) q
  obtain ⟨hZR,eStar,hstar,hquot⟩ := linear_point_section_marked_natural_quotient D S m
    hd hfix hX hK hLK.le hk hp hcard hmove hzero B A hBA hAU he
  change Z = R at hZR
  have hne : R ≠ ⊤ := by
    obtain ⟨a,ha,z,hz⟩ := hsurv
    exact linear_point_fixed_kernel_ne_top D S m hX hK hLK hk hcard B A a ha.2 z hz
  obtain ⟨e,heq⟩ := hquot.resolve_left (fun ht => hne (hZR.symm.trans ht))
  let π : C →* Multiplicative (Fin 2 → S.field.Carrier) :=
    e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hπk : π.ker = R := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact hZR
  have hπq (a) : π (q a) = eStar (pointFixedStarImage D S m A hAU a) := heq a
  have hindex : R.index = 16 := by
    rw [←hZR,Subgroup.index_eq_card,Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → S.field.Carrier) = 16
    rw [Nat.card_fun,Nat.card_fin,S.field.card_eq,hd]
    decide
  let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
    (hLK.le.trans (le_sup_left.trans le_sup_left))
  let r := (pointConstituentProjection D S m).comp
    (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left))
  have hπact (h : H) (u v : C)
      (hv : (v : Section B A) = sectionAction B A (inclusion hHJ h) u.val) :
      π v = Matrix.SL2.naturalAction S.field.Carrier (r h) (π u) := by
    obtain ⟨a,rfl⟩ := hqs u
    obtain ⟨hn,hh⟩ := linear_point_fixed_star_plus_action D S m f hLK.le hcard B A hAU h
    let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
      (hLK.le.trans (le_sup_left.trans le_sup_left))
    let b := conjugateFixed A (E.subgroupOf J) (inclusion hHJ h) hn a
    have hb : q b = v := Subtype.ext ((hh a).1.trans hv.symm)
    rw [←hb,hπq,hπq]
    exact hstar (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left) h)
      (pointFixedStarImage D S m A hAU a) (pointFixedStarImage D S m A hAU b) (hh a).2
  refine ⟨hqs,hindex,eStar,π,hπs,hπk,hπq,hπact,?_,?_⟩
  · intro w
    obtain ⟨c,hc⟩ := hπs (eStar w)
    obtain ⟨a,rfl⟩ := hqs c
    exact ⟨a,eStar.injective ((hπq a).symm.trans hc)⟩
  · intro P hP W _ τ t ht heq hirr hmove
    apply QuotientGroup.CommonImage.natural_simple_common_image (π.comp P.subtype) t ht r
      (linear_point_cubic_constituent_surjective D S m hcard) τ _ _ hirr hmove
    · intro h x
      obtain ⟨y,hy⟩ := hP h x
      exact ⟨y,heq h x y hy,hπact h x.val y.val hy⟩
    · intro x hx h
      have hxR : x.val ∈ R := hπk ▸ hx
      have hf := hxR ⟨inclusion hHJ h,h.property⟩
      exact (heq h x x hf.symm).symm


/-- The original faithful chief section has a nonzero natural cubic-fixed
quotient with exact fixed kernel and index sixteen. Every noncentral simple
subquotient of that cubic-fixed section has the same marked natural action.
The endpoint maps, full quotient action and surviving commutator are retained. -/
theorem linear_point_chief_natural_epimorphism
    (hd : S.field.degree = 2)
    (hfix : (flag D S m).Li 0 ≤ centralizer ((flag D S m).Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer ((flag D S m).Vi 0 : Set G)) K)
    (hLK : (flag D S m).Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0) ≤
      centralizer ((flag D S m).Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer ((flag D S m).Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let f := flag D S m
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual (f.Li 0) E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    U ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧
      ∃ hAU : A.val ≤ U.subgroupOf J,
      ∃ he : IsElementaryAbelian 2 (Section B A), let _ := he
      let _ : CommGroup (Section B A) :=
        { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
      ∃ ρ : Representation (ZMod 2)
        ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) (Additive (Section B A)),
        Representation.IsIrreducible ρ ∧ Function.Injective ρ ∧
        ρ.comp (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))) =
          (binarySectionRepresentation B A).comp
            (inclusion (show K ⊔ X ≤ J from le_sup_left)) ∧
        (let C := sectionFixed B A (E.subgroupOf J)
         let R := (sectionFixed B A (H.subgroupOf J)).subgroupOf C
         let q := fixedProjection B A (E.subgroupOf J)
         let hHJ : H ≤ J := ((localResidual_le E).trans inf_le_left).trans
           (hLK.le.trans (le_sup_left.trans le_sup_left))
         let r := (pointConstituentProjection D S m).comp
           (inclusion (show H ≤ f.Li 0 from (localResidual_le E).trans inf_le_left))
         Function.Surjective q ∧ R.index = 16 ∧
         ∃ eStar : (linearPointSetup D S m f).star U ≃* Multiplicative (Fin 2 → S.field.Carrier),
         ∃ π : C →* Multiplicative (Fin 2 → S.field.Carrier),
           Function.Surjective π ∧ π.ker = R ∧
           (∀ a, π (q a) = eStar (pointFixedStarImage D S m A hAU a)) ∧
           (∀ (h : H) (u v : C),
             (v : Section B A) = sectionAction B A (inclusion hHJ h) u.val →
             π v = Matrix.SL2.naturalAction S.field.Carrier (r h) (π u)) ∧
           Function.Surjective (pointFixedStarImage D S m A hAU) ∧
           ∀ (P : Subgroup C),
             (∀ (h : H) (x : P), ∃ y : P,
               (y.val : Section B A) = sectionAction B A (inclusion hHJ h) x.val.val) →
             ∀ (W : Type*) [CommGroup W] (τ : H →* MulAut W) (t : P →* W),
               Function.Surjective t →
               (∀ (h : H) (x y : P),
                 (y.val : Section B A) = sectionAction B A (inclusion hHJ h) x.val.val →
                 t y = τ h (t x)) →
               (∀ N : Subgroup W, (∀ h w, w ∈ N → τ h w ∈ N) → N = ⊥ ∨ N = ⊤) →
               (∃ h w, τ h w ≠ w) →
               ∃ e : W ≃* Multiplicative (Fin 2 → S.field.Carrier),
                 (∀ x : P, e (t x) = π x.val) ∧
                 ∀ h w, e (τ h w) = Matrix.SL2.naturalAction S.field.Carrier (r h) (e w)) ∧
        ∃ a : A.val, ((a : J) : G) ∈ U ⊓ centralizer (E : Set G) ∧
          ∃ z : (X ⊓ K : Subgroup G),
            ⁅inclusion (show X ⊓ K ≤ J from
              inf_le_left.trans (le_sup_right.trans le_sup_left)) z,(a : J)⁆ ∉ B.val := by
  intro f E H U J
  obtain ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,hcover,hsurv⟩ :=
    linear_point_chief_marked_natural_cover D S m hd hfix hX hK hLK.le hk hp hcard hmove hzero
  let _ := he
  let _ : CommGroup (Section B A) :=
    { (inferInstance : Group (Section B A)) with mul_comm := mul_comm' }
  refine ⟨hU,B,A,hZB,hBA,hAU,he,ρ,hirr,hfaith,hρ,?_,hsurv⟩
  exact section_natural_epimorphism D S m hd hfix hX hK hLK hk hp hcard hmove hzero
    B A hBA.le hAU he hcover.1 hsurv

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
