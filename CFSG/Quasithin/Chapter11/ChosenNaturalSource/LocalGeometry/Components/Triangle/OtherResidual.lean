module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ResidualLifts
public import Theory.GroupTheory.NormalSylowQuotientAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership

/-!
# The unique other residual in the field-four triangle

Mark K/O₂(K) so that the image of T intersect K is the standard Sylow.
The first residual selects one of the two canonical lifts; define K₀ by
the other. The original Sylow fixes the first lift and the marked Sylow,
so it fixes K₀. The original nonzero flag line supplies the nontrivial
two-core required by the Chapter 1 local family.

The source application proves uniqueness among the actual members of
L(G,T) contained in K and distinct from K and L₁. It also proves He
membership, the literal PSL₂(4) quotient, and K = ⟨L₁,K₀⟩. Its hypotheses
are the genuine exceptional setup (*) and the preceding flag quotient.
It does not assume a second parabolic or a triangle witness.

Constructing the component I = ⟨K₀,L₂⟩, proving its maximality and
faithfulness, excluding the SL₃(4) configuration and proving both opposite
G₂(4)/Sp₄(4) orientations remain with qt-d-1222-natural-relative-components.
Earlier flag inputs retain their source owner and final discharge in
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, the first triangle-construction paragraph on printed p.762.
-/


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterA.Section03 CFSG.Quasithin.Chapter1.Section02
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem preserves_subgroupOf {K B : Subgroup G}
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

/-- Construct the other parabolic residual in the original ambient group.
The common nontrivial two-subgroup supplies the genuine Chapter 1 local-family clause. -/
theorem exists_other_local (T : Sylow 2 G) {K B U : Subgroup G}
    (hK : (⊤ : Subgroup K).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hB : B ∈ localCComponents (T : Subgroup G)) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hU : U ≠ ⊥) (hUT : U ≤ (T : Subgroup G))
    (hNU : K ⊔ (T : Subgroup G) ≤ normalizer (U : Set G))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ∃ K₀ : Subgroup G, K₀ ∈ CFSG.Quasithin.Chapter1.L G T ∧ K₀ < K ∧ K₀ ≠ B ∧
      (∀ J : Subgroup G, J ∈ localCComponents (T : Subgroup G) → J < K → J ≠ B → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ B ⊔ K₀ = K ∧
      ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 := by
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
  have hBne : B.subgroupOf K ≠ ⊤ := fun he => hBK.not_ge (subgroupOf_eq_top.mp he)
  obtain ⟨b,hb⟩ := local_eq_rootLift hF r hr P hrP hkP hK hBP hBne
  let C := rootLift r (!b)
  let K₀ := C.map K.subtype
  have hCK : K₀ ≤ K := map_subtype_le C
  have hCsub : K₀.subgroupOf K = C := comap_map_eq_self_of_injective K.subtype_injective C
  have hCne : K₀ ≠ K := by
    intro he
    apply rootLift_ne_top hF r hr (!b)
    change C = ⊤
    rw [←hCsub,he,subgroupOf_self]
  have hCB : K₀ ≠ B := by
    intro he
    have hh : rootLift r (!b) = rootLift r b := hCsub.symm.trans ((congrArg (fun J : Subgroup G => J.subgroupOf K) he).trans hb)
    have hn := rootLift_injective hF r hr hh
    cases b <;> simp at hn
  have hnorm : (T : Subgroup G) ≤ normalizer (K₀ : Set G) := by
    intro t ht
    let tK : normalizer (K : Set G) := ⟨t,hTK ht⟩
    let actor := K.normalizerMonoidHom tK
    have hPa : (P : Subgroup K).map actor.toMonoidHom = P := by
      rw [hP]
      exact preserves_subgroupOf tK ((T : Subgroup G).le_normalizer ht)
    have hBa : (rootLift r b).map actor.toMonoidHom = rootLift r b := by
      rw [←hb]
      exact preserves_subgroupOf tK (hTB ht)
    have hCa := other_rootLift_fixed hF r hr P hrP hkP hK actor hPa b hBa
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hcomp : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp actor.toMonoidHom := by
      ext x
      rfl
    change (C.map K.subtype).map (MulAut.conj t).toMonoidHom = C.map K.subtype
    rw [map_map,hcomp,←map_map,hCa]
  have htopC : (⊤ : Subgroup C).IsCComponent := by
    have hh := (rootLift_component hF r hr (!b)).subgroupOf_of_le le_rfl (rootLift_le r (!b))
    simpa only [subgroupOf_self] using hh
  let cK : C ≃* K₀ := C.equivMapOfInjective K.subtype K.subtype_injective
  have htopK : (⊤ : Subgroup K₀).IsCComponent := by
    simpa only [map_top_of_surjective cK.toMonoidHom cK.surjective] using htopC.map_equiv cK
  have hlocal : K₀ ∈ CFSG.Quasithin.Chapter1.L G T := by
    let W := K₀ ⊔ (T : Subgroup G)
    let w := (subgroupOfEquivOfLe (show K₀ ≤ W from le_sup_left)).symm
    have htW : (⊤ : Subgroup (K₀.subgroupOf W)).IsCComponent := by
      simpa only [map_top_of_surjective w.toMonoidHom w.surjective] using htopK.map_equiv w
    let : (K₀.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le K₀.le_normalizer hnorm)
    refine ⟨?_,⟨T.subtype le_sup_right,?_⟩,?_⟩
    · simpa only [←MonoidHom.range_eq_map,range_subtype] using
        htW.map_subtype (inferInstance : (K₀.subgroupOf W).Normal).isSubnormal
    · simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    · intro he
      apply hU
      apply bot_unique
      have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT)
        (hUT.trans (show (T : Subgroup G) ≤ W from le_sup_right))
        ((sup_le_sup_right hCK (T : Subgroup G)).trans hNU)
      exact he ▸ hcore
  refine ⟨K₀,hlocal,lt_of_le_of_ne hCK hCne,hCB,?_,hnorm,?_,?_⟩
  · intro J hJ hJK hJB
    have hJP : J.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
      hP.symm ▸ SourceEmbeddings.local_restrict hJ hJK.le
    obtain ⟨d,hd⟩ := local_eq_rootLift hF r hr P hrP hkP hK hJP
      (fun he => hJK.not_ge (subgroupOf_eq_top.mp he))
    have hdb : d ≠ b := by
      intro he
      apply hJB
      have hh := congrArg (map K.subtype) ((hd.trans (congrArg (rootLift r) he)).trans hb.symm)
      simpa only [map_subgroupOf_eq_of_le hJK.le,map_subgroupOf_eq_of_le hBK.le] using hh
    have hd' : d = !b := by cases b <;> cases d <;> simp_all
    have hh := congrArg (map K.subtype) hd
    simpa only [map_subgroupOf_eq_of_le hJK.le,hd'] using hh
  · let := hK.perfect
    let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
      (f := (topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom) topEquiv.surjective
    have hh := congrArg (map K.subtype) (rootLift_sup hF r hr b)
    rw [Subgroup.map_sup,←hb,map_subgroupOf_eq_of_le hBK.le,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  · refine ⟨F,inferInstance,inferInstance,hF,?_⟩
    let cq := QuotientGroup.congr _ _ cK (pCore_map_iso 2 cK)
    exact ⟨cq.symm.trans ((rootLiftQuotient hF r hr (by rw [hrker]; exact pCore_isPGroup) (!b)).trans
      (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F))⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The first construction in 11.1.2(*): the unique other residual K₀,
with ambient local membership, relative Sylow invariance, He and generation. -/
theorem first_triangle_other_residual
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K : Subgroup G} (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ K₀ ∈ Chapter1.He G ∧
      f.Li 0 ⊔ K₀ = K ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 := by
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  obtain ⟨K₀,h₀,h₀K,h₀L,hu,hn,hgen,hsmall⟩ := Triangle.exists_other_local T ht hTK
    (flag_mem_local_of_model D S f 0 hm).1 hLK (f.sylow_normalizes_Li 0)
    (f.V_ne_bot 0) ((D.centralQuotientPreimage_le _).trans D.le_sylow)
    (sup_le hK.1.1 (f.invariant 0)) hk
  have hHe : K₀ ⊔ (T : Subgroup G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T)
      ⟨h₀.2.2,fun _ hx => (show (T : Subgroup G) ≤ K₀ ⊔ (T : Subgroup G) from le_sup_right) hx⟩
  have h₀He : K₀ ∈ Chapter1.He G := Chapter1.lemma_1_1_3_1 hHe
    (fun he => h₀.1.ne_bot (by rw [he]; exact bot_subgroupOf _)) le_sup_left h₀.1.subnormal
  exact ⟨K₀,h₀,h₀K.le,h₀K.ne,h₀L,
    fun J hJ hJK hne hJL => hu J hJ.1 (lt_of_le_of_ne hJK hne) hJL,hn,h₀He,hgen,hsmall⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
