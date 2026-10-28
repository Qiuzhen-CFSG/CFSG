module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexSieveSp4
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PCorePrimeToIndex
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Both GL₂(4) local quotients in the symplectic triangle

A normal A₅ subgroup of index three has trivial outer action. Its
centralizer is a direct factor of order three, identifying the whole
group with GL₂(4). An order-nine normalizing Cartan with cubic
intersection gives precisely that index after the original two-core is
removed. The proof also identifies the join's embedded two-core with
the smaller residual's embedded two-core.

For K₀, an actor preserving L₁ and T ∩ L₁ preserves T ∩ K modulo
O₂(K). The two canonical PSL₃(4) residual lifts then force it to
preserve K₀. Apply this to the original X. The checked symplectic
Cartan splitting gives the second cubic intersection, so the same
quotient argument supplies both K₀X/O₂(K₀) and L₂X/O₂(L₂).

The final consumer starts with the original nontrivial common normal Q
and places both marked proper locals in the literal I = K₀ ∨ L₂,
retaining relative normality, He, faithful-local membership and both
three-ranks. It does not assume either GL₂ model. The remaining A.3.14
comparison, common-normal existence, SL₃(4) exclusion, maximality and
both orientations remain with qt-d-1222-natural-relative-components.
Earlier flag and Cartan premises retain their existing producers and
final discharge by qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--764, especially the two GL₂(4) markings on p.763.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

private theorem five_outer_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5))) := by
  let A := alternatingGroup (Fin 5)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [← A.index_eq_card, alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨s, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A s, rfl⟩

private theorem normal_five_index_three {H : Type*} [Group H] [Finite H]
    (B : Subgroup H) [B.Normal] (eB : B ≃* alternatingGroup (Fin 5))
    (hi : B.index = 3) : Nonempty (H ≃* (alternatingGroup (Fin 5) × Multiplicative (ZMod 3))) := by
  let C := centralizer (B : Set H)
  have hz : center B = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have hh := (centerCongr eB ⟨b,hb⟩).property
    change eB b ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eB.map_eq_one_iff.mp hh
  have hd : Disjoint B C := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hb,hc⟩
    have hx : (⟨x,hb⟩ : B) ∈ center B :=
      mem_center_iff.mpr (fun b => Subtype.ext (hc b b.property))
    rw [hz,mem_bot] at hx
    exact congrArg Subtype.val hx
  have hq : IsPGroup 3 (H ⧸ B) := IsPGroup.of_card (n := 1) (by
    rw [← B.index_eq_card,hi]; rfl)
  have ho : IsPGroup 2 (MulAut.Outer B) :=
    five_outer_two.of_equiv (MulAut.outerCongr eB).symm
  have htriv : ∀ x, MulAut.outerAction B x = 1 := by
    have hh := IsPGroup.disjoint_of_coprime
      (hq.of_surjective (MulAut.outerAction B).rangeRestrict
        (MulAut.outerAction B).rangeRestrict_surjective)
      (ho.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
    exact fun x => (Subgroup.disjoint_def.mp hh) ⟨x,rfl⟩ (mem_top _)
  have hgen : B ⊔ C = ⊤ := by
    apply top_unique
    intro x _
    rw [← MulAut.conjNormal_comap_innerSubgroup B]
    exact (QuotientGroup.eq_one_iff (MulAut.conjNormal (H := B) x)).mp (htriv (QuotientGroup.mk' B x))
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C hd
    (le_centralizer_iff.mp (le_refl C))
  let a : B × C ≃* H := e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv)
  have hcard : Nat.card B * Nat.card C = Nat.card B * 3 := by
    rw [←Nat.card_prod,Nat.card_congr a.toEquiv,←hi,B.card_mul_index]
  have hc : Nat.card C = 3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard
  let c : C ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hc (Nat.card_zmod 3)
  exact ⟨a.symm.trans (eB.prodCongr c)⟩

private def detKernelEquiv (F : Type*) [Field F] :
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker ≃* SL(2,F) where
  toFun g := ⟨g.val.val,congrArg Units.val g.property⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.toGL g,Matrix.SpecialLinearGroup.coeToGL_det g⟩
  left_inv g := by apply Subtype.ext; apply Units.ext; rfl
  right_inv g := rfl
  map_mul' g h := rfl

private theorem gl_four_equiv (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nonempty (GL (Fin 2) F ≃* (alternatingGroup (Fin 5) × Multiplicative (ZMod 3))) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  let B := (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eB : B ≃* alternatingGroup (Fin 5) :=
    (detKernelEquiv F).trans ((Theory.PSL2.sl2QuotientEquiv F).trans e)
  have hi : B.index = 3 := by
    rw [B.index_eq_card,Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective _ Matrix.GeneralLinearGroup.det_surjective).toEquiv,
      Nat.card_units,hF]
  exact normal_five_index_three B eB hi

/-- A group-dependent model for the literal local quotient. -/
def IsGLTwoFour (A : Type*) [Group A] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (A ≃* GL (Fin 2) F)

/-- Construct or use the model predicate through its actual field equivalence. -/
theorem isGLTwoFour_iff (A : Type*) [Group A] :
    IsGLTwoFour A ↔ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (A ≃* GL (Fin 2) F) := Iff.rfl

/-- A normal PSL₂(4) section of index three gives the literal GL₂(4) quotient. -/
private theorem normal_psl_two_four_index_three {H : Type*} [Group H] [Finite H]
    (B : Subgroup H) [B.Normal]
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) (hi : B.index = 3) :
    pCore 2 H = B.pCoreIn 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty ((H ⧸ pCore 2 H) ≃* GL (Fin 2) F) := by
  have hcore : pCore 2 H ≤ B :=
    (pCore_le_map_pCore_of_prime_not_dvd_index B (by rw [hi]; decide)).trans (map_subtype_le _)
  refine ⟨pCore_eq_map_of_normal_of_le 2 B hcore,?_⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  have hc : (q.subgroupMap B).ker = pCore 2 B := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_eq_comap_of_normal 2 B).symm
  let eC : (B ⧸ pCore 2 B) ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap B) (q.subgroupMap_surjective B))
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let : C.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  have hiC : C.index = 3 := by
    rw [show C = B.map q from rfl,B.index_map_eq (QuotientGroup.mk'_surjective _)
      (by simpa only [q,QuotientGroup.ker_mk'] using hcore),hi]
  obtain ⟨a⟩ := normal_five_index_three C (eC.symm.trans (e.trans e5)) hiC
  obtain ⟨b⟩ := gl_four_equiv F hF
  exact ⟨F,inferInstance,inferInstance,hF,⟨a.trans b.symm⟩⟩

/-- The order-nine supplement and its cubic intersection give the source
index three, with the original residual's embedded two-core unchanged. -/
theorem residual_cartan_gl_two_four {G : Type*} [Group G] [Finite G]
    (B X : Subgroup G) (hn : X ≤ normalizer (B : Set G))
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hX : Nat.card X = 9) (hi : Nat.card (X ⊓ B : Subgroup G) = 3) :
    (B ⊔ X : Subgroup G).pCoreIn 2 = B.pCoreIn 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (((B ⊔ X : Subgroup G) ⧸ pCore 2 (B ⊔ X : Subgroup G)) ≃* GL (Fin 2) F) := by
  let H := B ⊔ X
  let C := B.subgroupOf H
  let e := subgroupOfEquivOfLe (show B ≤ H from le_sup_left)
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4 := by
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans a⟩⟩
  have hidx : C.index = 3 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B X hn
    rw [inf_comm B X,hi,hX] at hh
    have hCcard : Nat.card C = Nat.card B := Nat.card_congr e.toEquiv
    have hc := C.card_mul_index
    rw [hCcard] at hc
    have hmul : Nat.card B * (C.index * 3) = Nat.card B * 9 := by
      calc
        _ = 3 * (Nat.card B * C.index) := by ring
        _ = 3 * Nat.card H := by rw [hc]
        _ = _ := hh.symm
    have hh' := Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    omega
  obtain ⟨hcore,hm⟩ := normal_psl_two_four_index_three C hC hidx
  refine ⟨?_,hm⟩
  have he := congrArg (map H.subtype) hcore
  change (pCore 2 H).map H.subtype = _
  rw [he]
  change ((pCore 2 C).map C.subtype).map H.subtype = _
  rw [map_map,show H.subtype.comp C.subtype = B.subtype.comp e.toMonoidHom from rfl,
    ←map_map,pCore_map_iso 2 e]
  rfl

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterA.Section03
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem preserves_restriction {K B : Subgroup G}
    (g : normalizer (K : Set G)) (hg : (g : G) ∈ normalizer (B : Set G)) :
    (B.subgroupOf K).map (K.normalizerMonoidHom g).toMonoidHom = B.subgroupOf K := by
  have hf (u : normalizer (K : Set G)) (hu : (u : G) ∈ normalizer (B : Set G))
      {x : K} (hx : x ∈ B.subgroupOf K) :
      K.normalizerMonoidHom u x ∈ B.subgroupOf K := by
    change (K.normalizerMonoidHom u x : G) ∈ B
    rw [normalizerMonoidHom_apply_apply_coe]
    exact (hu x).mp hx
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hf g hg hy
  · intro hx
    refine ⟨K.normalizerMonoidHom g⁻¹ x,hf g⁻¹ ((normalizer (B : Set G)).inv_mem hg) hx,?_⟩
    rw [map_inv K.normalizerMonoidHom g]
    exact (K.normalizerMonoidHom g).apply_symm_apply x

/-- An actor fixing one marked residual and its Sylow intersection fixes
both residuals of the same PSL₃(4) component. -/
theorem other_local_marking_of_normalizes_intersection (T : Sylow 2 G) {K B C X : Subgroup G}
    (hK : (⊤ : Subgroup K).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hB : B ∈ localCComponents (T : Subgroup G)) (hBK : B < K)
    (hC : C ∈ localCComponents (T : Subgroup G)) (hCK : C < K)
    (hXK : X ≤ normalizer (K : Set G)) (hXB : X ≤ normalizer (B : Set G))
    (hXP : X ≤ normalizer (((T : Subgroup G) ⊓ B : Subgroup G) : Set G))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) : X ≤ normalizer (C : Set G) ∧
      ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by simpa using hF)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (P.mapSurjective hq)
    (unipotentSylow F (by decide : 0 < 2) (by simpa using hF))
  let a := MulAut.conj g
  let r := a.toMonoidHom.comp q
  have hr : Function.Surjective r := a.surjective.comp hq
  have hrker : r.ker = pCore 2 K := by
    ext x
    change a (e (QuotientGroup.mk' (pCore 2 K) x)) = 1 ↔ _
    rw [a.map_eq_one_iff,e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsNilpotent r.ker := by rw [hrker]; exact pCore_isNilpotent
  have hrP : (P : Subgroup K).map r = unipotent F := by
    rw [←map_map]
    exact congrArg Sylow.toSubgroup hg
  have hkP : r.ker ≤ (P : Subgroup K) := by
    rw [hrker]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hBP : B.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ SourceEmbeddings.local_restrict hB hBK.le
  have hCP : C.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ SourceEmbeddings.local_restrict hC hCK.le
  obtain ⟨b,hb⟩ := local_eq_rootLift hF r hr P hrP hkP hK hBP
    (fun he => hBK.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨d,hd⟩ := local_eq_rootLift hF r hr P hrP hkP hK hCP
    (fun he => hCK.not_ge (subgroupOf_eq_top.mp he))
  have hi : ((P : Subgroup K) ⊓ B.subgroupOf K).map r = unipotent F := by
    rw [hb,inf_comm,map_inf_of_ker_le r (rootLift r b) P hkP,hrP,rootLift_map hF r hr]
    exact inf_eq_right.mpr (unipotent_le_rootLocal F b)
  have hdecomp : (P : Subgroup K) = ((P : Subgroup K) ⊓ B.subgroupOf K) ⊔ pCore 2 K := by
    have hh := congrArg (comap r) (hi.trans hrP.symm)
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hkP,hrker] at hh
    exact hh.symm
  have hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4 := by
    let u := subgroupOfEquivOfLe hCK.le
    let v := MulEquiv.subgroupCongr hd
    exact ⟨F,inferInstance,inferInstance,hF,⟨
      (QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).symm.trans
        ((QuotientGroup.congr _ _ v (pCore_map_iso 2 v)).trans
          ((rootLiftQuotient hF r hr (by rw [hrker]; exact pCore_isPGroup) d).trans
            (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F)))⟩⟩
  refine ⟨?_,hmC⟩
  intro x hx
  let xK : normalizer (K : Set G) := ⟨x,hXK hx⟩
  let actor := K.normalizerMonoidHom xK
  have hBi : (B.subgroupOf K).map actor.toMonoidHom = B.subgroupOf K :=
    preserves_restriction xK (hXB hx)
  have hPi : ((P : Subgroup K) ⊓ B.subgroupOf K).map actor.toMonoidHom =
      (P : Subgroup K) ⊓ B.subgroupOf K := by
    rw [hP]
    exact preserves_restriction xK (hXP hx)
  have hPa : (P : Subgroup K).map actor.toMonoidHom = P := by
    conv_lhs => rw [hdecomp]
    rw [Subgroup.map_sup,hPi,pCore_map_iso,hdecomp.symm]
  have hBa : (rootLift r b).map actor.toMonoidHom = rootLift r b := hb ▸ hBi
  have hCa : (rootLift r d).map actor.toMonoidHom = rootLift r d := by
    by_cases he : d = b
    · exact he ▸ hBa
    · have he' : d = !b := (Bool.not_eq_iff.mpr (Ne.symm he)).symm
      rw [he']
      exact other_rootLift_fixed hF r hr P hrP hkP hK actor hPa b hBa
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hcomp : (MulAut.conj x).toMonoidHom.comp K.subtype = K.subtype.comp actor.toMonoidHom := by
    ext y
    rfl
  rw [←hd] at hCa
  have hh := congrArg (map K.subtype) hCa
  rw [map_map,←hcomp,←map_map,map_subgroupOf_eq_of_le hCK.le] at hh
  exact hh

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The two local quotients used on p.763, with each smaller two-core
identified in the actual residual–Cartan join. -/
theorem sp4_triangle_local_gl_markings
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
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
    rw [(Coordinates.sp4 m).cartan_card hX,hfour]
    norm_num
  have hcard₀ : Nat.card (X ⊓ K₀ : Subgroup G) = 3 := h₀ ▸ hc
  have hcard₁ : Nat.card (X ⊓ f.Li 0 : Subgroup G) = 3 := h₁ ▸ hc
  have hcard₂ : Nat.card (X ⊓ f.Li 1 : Subgroup G) = 3 := by
    obtain ⟨hgen,hdis⟩ := sp4_cartan_split D S m f hX
    let e := (Coordinates.sp4 m).cartanTorusEquiv hX
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
  exact ⟨hn₀,hm₀,hc₀,hg₀,hc₂,hg₂⟩

/-- The original common-normal construction supplies the actual third vertex
with both proper GL₂-marked locals. This is the input to the remaining
A.3.14 comparison, not the three-model recognition conclusion. -/
theorem sp4_triangle_marked_locals_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    Source.NormalComponentIn (I ⊔ (T : Subgroup G)) I ∧
      I ∈ Chapter1.L G T ∧ I ∈ Chapter1.He G ∧ I ∈ MainForward.faithfulLocalComponents T ∧
      primeRank 3 I = 2 ∧ primeRank 3 (I ⧸ pCore 2 I) = 2 ∧
      ∀ B : Subgroup G, B = K₀ ∨ B = f.Li 1 →
        B < I ∧ B ⊔ X ≤ I ∧ X ≤ normalizer (B : Set G) ∧
        ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 ∧
        (B ⊔ X : Subgroup G).pCoreIn 2 = B.pCoreIn 2 ∧
        IsGLTwoFour ((B ⊔ X : Subgroup G) ⧸ pCore 2 (B ⊔ X : Subgroup G)) := by
  intro I
  obtain ⟨hI,hIL,hIH,hIf,hXI,hr,hrq⟩ := sp4_triangle_join_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hn₀,hm₀,hc₀,hg₀,hc₂,hg₂⟩ := sp4_triangle_local_gl_markings
    D S m f hu hm₁ hm₂ hfour hX hK hLK hK₀ hK₀K hk hp
  obtain ⟨hlt₀,hlt₂,_,_⟩ := sp4_triangle_proper_residuals
    D S m f hu hm₁ hfour hX hK hLK hK₀ hK₀K hk hp
  refine ⟨hI,hIL,hIH,hIf,hr,hrq,?_⟩
  intro B hB
  rcases hB with rfl | rfl
  · exact ⟨hlt₀,sup_le le_sup_left hXI,hn₀,hm₀,hc₀,hg₀⟩
  · have hn₂ : X ≤ normalizer (f.Li 1 : Set G) := by
      have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
        le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
      exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
    exact ⟨hlt₂,sup_le le_sup_right hXI,hn₂,by simpa [hfour] using hm₂,hc₂,hg₂⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
