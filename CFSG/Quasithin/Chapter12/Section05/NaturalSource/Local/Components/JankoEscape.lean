module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.LargeEscape
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowLift
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The Janko escape and the complete strict point-component argument

The full original Sylow action preserves a Mathieu local subgroup in the
J₄ component quotient. Pulling it back retains the whole covering kernel.
This seed cannot normalize L: its intersection with L maps trivially to
M₂₄, since 23 does not divide |L|. Squares in the resulting two-core lie in
O₂(K₁), which would make the original point Sylow quotient elementary,
contrary to its dihedral order-eight section. The native Mathieu cubic
parabolics therefore lift to an escaping cubic overgroup of the original T.

Combining this with the linear, Mathieu and radical escapes completes the
conditional implication 12.5.11(1) ⇒ 12.5.11(2), including relative normality
of L₁ in G₁. The source-parameter applications use the existing generation
exclusion, whose premises include Structural1222At and G₃,G₆ ≤ N_G(L).
The two general normalizer containments remain with qt-d-1251-local; they
are not inferred circularly from this application. The earlier structural
input belongs to qt-d-1222-source, and qt-d-1251-source owns final assembly.

Source: Aschbacher--Smith, 12.5.3 and 12.5.11(2), printed pp.818 and 821.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

include s in
private theorem component_not_twentyThree : ¬ 23 ∣ Nat.card L := by
  have hc : Nat.card (L ⧸ pCore 2 L) = 9999360 := by
    rw [←s.marking.componentActor_ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        s.marking.componentActor s.marking.componentActor_surjective).toEquiv]
    change Nat.card SL(5,ZMod 2) = _
    rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 5).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  intro hd
  rw [←(pCore 2 L).card_mul_index,index_eq_card,hc] at hd
  rcases (by decide : Nat.Prime 23).dvd_mul.mp hd with hd | hd
  · obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := L))
    rw [hn] at hd
    have hh := (by decide : Nat.Prime 23).dvd_of_dvd_pow hd
    norm_num at hh
  · norm_num at hd

/-- The actual Mathieu local preimage in a Janko point component retains
its Sylow actor, quotient and the squares of its two-core. -/
theorem exists_mathieu_seed_in_janko_point_component
    {K : Subgroup G} (hK : K ≤ s.marking.Gi 1)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    ∃ R : Subgroup G, R ≤ K ∧ (T : Subgroup G) ⊓ K ≤ R ∧
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Sporadic.Mathieu.M24) ∧
      (∀ r : R, r ∈ pCore 2 R → (r : G) ^ 2 ∈ K.pCoreIn 2) := by
  have hn := s.sylow_le_G₁.trans ((normal_subgroupOf_iff_le_normalizer hK).mp hN)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  obtain ⟨B,hPB,hinv,⟨eb⟩,hsq⟩ :=
    Janko4.LocalStructure.exists_sylow_mathieu_seed_of_two_core hm.some P
  let R := B.map K.subtype
  let e : B ≃* R := B.equivMapOfInjective K.subtype K.subtype_injective
  refine ⟨R,map_subtype_le B,?_,?_,?_,?_⟩
  · intro t ht
    have hp : (⟨t,ht.2⟩ : K) ∈ (P : Subgroup K) := by
      rw [hP]
      exact ht.1
    exact mem_map_of_mem K.subtype (hPB hp)
  · intro t ht
    let a := K.normalizerMonoidHom ⟨t,hn ht⟩
    have haP : (P : Subgroup K).map a.toMonoidHom = P := by
      rw [hP]
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        change (a x : G) ∈ (T : Subgroup G)
        rw [normalizerMonoidHom_apply_apply_coe]
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hx)
          ((T : Subgroup G).inv_mem ht)
      · exact (Nat.card_congr (a.subgroupMap ((T : Subgroup G).subgroupOf K)).toEquiv).le
    have haB := hinv a haP
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp a.toMonoidHom := by
      ext x
      exact (normalizerMonoidHom_apply_apply_coe K ⟨t,hn ht⟩ x).symm
    change (B.map K.subtype).map (MulAut.conj t).toMonoidHom = B.map K.subtype
    rw [map_map,he,←map_map,haB]
  · exact ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans eb⟩
  · intro r hr
    have hb : e.symm r ∈ pCore 2 B :=
      (pCore_map_iso 2 e.symm) ▸ mem_map_of_mem e.symm.toMonoidHom hr
    have hh := hsq (e.symm r) hb
    have he : ((e.symm r : B) : K).val = (r : G) :=
      congrArg R.subtype (e.apply_symm_apply r)
    have hh' := mem_map_of_mem K.subtype hh
    change (((e.symm r : B) : K) : G) ^ 2 ∈ K.pCoreIn 2 at hh'
    rwa [he] at hh'

/-- The original point Sylow prevents a Mathieu seed with elementary core
modulo O₂(K) from normalizing L. -/
theorem mathieu_point_seed_not_le_M
    {K R : Subgroup G} (hLK : s.marking.Li 1 ≤ K)
    (hTR : (T : Subgroup G) ⊓ K ≤ R)
    (hm : Nonempty ((R ⧸ pCore 2 R) ≃* Sporadic.Mathieu.M24))
    (hsq : ∀ r : R, r ∈ pCore 2 R → (r : G) ^ 2 ∈ K.pCoreIn 2) :
    ¬ R ≤ s.marking.M := by
  intro hRM
  let N := L.subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer hRM
  let f := hm.some.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := hm.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : f.ker = pCore 2 R := by
    rw [MonoidHom.ker_comp_of_injective _ _ hm.some.injective,QuotientGroup.ker_mk']
  let : IsSimpleGroup Sporadic.Mathieu.M24 := Sporadic.Mathieu.m24_isSimpleGroup
  let : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hN0 : N.map f = ⊥ := by
    rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with h0 | htop
    · exact h0
    · have hd : 23 ∣ Nat.card N := by
        have hd := card_map_dvd N f
        rw [htop,card_top,Sporadic.Mathieu.m24_order] at hd
        exact dvd_trans (by norm_num) hd
      let j : N →* L :=
        { toFun := fun x => ⟨((x : R) : G),x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hj : Function.Injective j := fun x y he => Subtype.ext (Subtype.ext (show ((x : R) : G) = ((y : R) : G) from congrArg L.subtype he))
      exact (s.component_not_twentyThree (hd.trans (card_dvd_of_injective j hj))).elim
  have hNc : N ≤ pCore 2 R := by
    rw [←hfker]
    exact (Subgroup.map_eq_bot_iff _).mp hN0
  let B := s.marking.Li 1
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T B
    (s.sylow_normalizes_Li 1 (.inl rfl))
  let j := inclusion hLK
  let N0 := (pCore 2 K).comap j
  have hN0c : N0 ≤ pCore 2 B :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective j (inclusion_injective hLK)⟩
  have hPpow (x : B) (hx : x ∈ (P : Subgroup B)) : x ^ 2 ∈ pCore 2 B := by
    have hxT : (x : G) ∈ (T : Subgroup G) := by
      have hx' : x ∈ (T : Subgroup G).subgroupOf B := hP ▸ hx
      exact hx'
    have hxR : (x : G) ∈ R := hTR ⟨hxT,hLK x.property⟩
    have hc := hNc (show (⟨(x : G),hxR⟩ : R) ∈ N from s.marking.Li_le_L 1 x.property)
    have hsqx := hsq ⟨(x : G),hxR⟩ hc
    obtain ⟨k,hk,he⟩ := hsqx
    apply hN0c
    change j (x ^ 2) ∈ pCore 2 K
    have he' : k = j (x ^ 2) := Subtype.ext he
    exact he' ▸ hk
  let e1 : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.SL := s.marking.LiCoreEquiv 1 (.inl rfl)
  let q := Matrix.PSL3Two.equiv.toMonoidHom.comp
    (e1.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
  have hq : Function.Surjective q := Matrix.PSL3Two.equiv.surjective.comp
    (e1.surjective.comp (QuotientGroup.mk'_surjective _))
  let Q := P.mapSurjective hq
  have hpow (z : Q) : z ^ 2 = 1 := by
    obtain ⟨x,hx,hxz⟩ := z.property
    apply Subtype.ext
    change (z : Matrix.PSL3Two.PSL) ^ 2 = 1
    rw [←hxz,←map_pow]
    have hh : QuotientGroup.mk' (pCore 2 B) (x ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hPpow x hx)
    change Matrix.PSL3Two.equiv (e1 (QuotientGroup.mk' (pCore 2 B) (x ^ 2))) = 1
    rw [hh,map_one,map_one]
  obtain ⟨ed⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral Q
  have hh := congrArg ed (hpow (ed.symm (DihedralGroup.r (1 : ZMod 4))))
  have hbad : (DihedralGroup.r (1 : ZMod 4)) ^ 2 = 1 := by
    simpa only [map_pow,map_one,ed.apply_symm_apply] using hh
  exact (by decide : (DihedralGroup.r (1 : ZMod 4)) ^ 2 ≠ 1) hbad

/-- The Janko point row supplies an escaping cubic overgroup of the original
full Sylow subgroup, inside the original K₁T. -/
theorem exists_cubic_overgroup_of_janko_point_component
    {K : Subgroup G} (hK : K ≤ s.marking.Gi 1)
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    ∃ J : Subgroup G, (T : Subgroup G) ≤ J ∧ J ≤ K ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex J = 3 ∧ ¬ J ≤ s.marking.M := by
  obtain ⟨R,hRK,hTR,hnR,⟨er⟩,hsq⟩ := s.exists_mathieu_seed_in_janko_point_component hK hN hm
  obtain ⟨J,hTJ,hJR,hi,hJM⟩ :=
    Sporadic.Mathieu.M24ValueBoundParabolics.exists_cubic_overgroup T R s.marking.M
      D.sylow_normalizes_component hnR er (s.mathieu_point_seed_not_le_M hLK hTR ⟨er⟩ hsq)
  exact ⟨J,hTJ,hJR.trans (sup_le_sup_right hRK _),hi,hJM⟩

/-- The native Mathieu seed completes the J₄ generation-one escape. -/
theorem exists_generation_one_of_janko_point_component
    {K : Subgroup G} (hK : K ≤ s.marking.Gi 1)
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ K ⊔ (T : Subgroup G) ∧ ChapterE.generationParameter H = 1 := by
  obtain ⟨J,hTJ,hJK,hi,hJM⟩ := s.exists_cubic_overgroup_of_janko_point_component hK hLK hN hm
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (T : Subgroup G).isSolvable_of_relIndex_le_four J (by omega)
  obtain ⟨H,hH,hHJ,hgen⟩ := s.exists_generation_one_of_solvable_point_overgroup hTJ
    (hJK.trans (sup_le hK s.sylow_le_G₁)) hJM
  exact ⟨H,hH,hHJ.trans hJK,hgen⟩

/-- Every strict source point-component enlargement supplies the original
solvable generation-one escape, in all four source rows. -/
theorem exists_generation_one_of_strict_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ K ⊔ (T : Subgroup G) ∧ ChapterE.generationParameter H = 1 := by
  cases s.point_component_alternative_from_source h hK hLK hN with
  | equal he => exact (hne he).elim
  | large _ hm _ =>
    rcases hm with hm | hm | hm
    · exact s.exists_generation_one_of_strict_linear_point_component h hK hLK hN hne hm
    · exact s.exists_generation_one_of_strict_mathieu_point_component hK hLK hN hne hm
    · exact s.exists_generation_one_of_janko_point_component hK.1 hLK hN hm
  | radical _ _ hm =>
    obtain ⟨H,hH,_,hHK,hgen⟩ := s.exists_generation_one_of_strict_radical_point_component
      h hK hLK hN hne (s.point_radical_alternative_not_quasisimple h hK hm)
    exact ⟨H,hH,hHK,hgen⟩

/-- All source alternatives now give K₁ = L₁ under the genuine
12.5.11(1) exclusion, without assuming normalizer control or LocalComponents. -/
theorem point_component_eq_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) : s.marking.Li 1 = K := by
  by_contra hne
  obtain ⟨H,hH,_,hgen⟩ := s.exists_generation_one_of_strict_point_component h hK hLK hN hne
  exact hex H hH hgen

/-- Literal equality for any original containing point component, using
only the previously proved source parameters and both normalizer containments. -/
theorem point_component_eq_of_source_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    s.marking.Li 1 = K := by
  apply s.point_component_eq_of_generation_exclusion h hK hLK hN
  intro H hH
  exact s.generation_ne_one_from_local_source h structural hG₃ hG₆ hH

/-- The original point residual is a normal C-component after the genuine
source generation exclusion; the full source component construction is used. -/
theorem point_component_normal_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) :
    s.marking.Li 1 ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal := by
  obtain ⟨c⟩ := s.local_components_from_source h
  have he := s.point_component_eq_of_generation_exclusion h
    (c.component 1 (.inl rfl)) (c.contains 1 (.inl rfl)) (c.normal 1 (.inl rfl)) hex
  exact he.symm ▸ ⟨c.component 1 (.inl rfl),c.normal 1 (.inl rfl)⟩

/-- The complete source 12.5.11(2) implication retains precisely the earlier
structural and normalizer premises of 12.5.11(1). -/
theorem point_component_normal_of_source_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M) :
    s.marking.Li 1 ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧
      ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal := by
  apply s.point_component_normal_of_generation_exclusion h
  intro H hH
  exact s.generation_ne_one_from_local_source h structural hG₃ hG₆ hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
