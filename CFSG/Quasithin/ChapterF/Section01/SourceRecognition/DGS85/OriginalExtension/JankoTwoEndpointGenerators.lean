module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoGeneratorRelations
/-!
# The source Hall–Janko generators in the original endpoints

A compatible reduced comparison transports the concrete generators across
both Borel inclusion squares. Three intermediate elements in the full
reduced Borel carry the mixed word z^(dt) without assuming an ambient
isomorphism between the completions. Core preservation then puts q in the
original first-core cubic commutator and z in the center of the original
second core. Adjoining the full original Borel recovers both endpoints.

The two endpoint indices are arbitrary, retaining both orientations.
Source: DGS, Groups and Graphs (1985), (15.3)(v),(vi), printed p.229.
Genuine compatible reduced recognition remains explicit. Aligning the
outer involution with this generating tuple, proving the order-twelve
product, and constructing the Aut(J₂) parabolic comparison remain separate
parts of the original-extension argument.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations
private theorem ambient_generate {A : Type*} [Group A] (P : Subgroup A)
    {n : ℕ} (g : Fin n → P) (hg : closure (Set.range g)=⊤) :
    closure (Set.range (fun i => (g i:A)))=P := by
  have hh := congrArg (Subgroup.map P.subtype) hg
  rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,P.range_subtype] at hh
  exact hh

private theorem map_vec4 {A D : Type*} (f : A → D) (a b c d : A) :
    (fun i => f (![a,b,c,d] i))=![f a,f b,f c,f d] := by
  funext i
  fin_cases i <;> rfl
private theorem map_vec5 {A D : Type*} (f : A → D) (a b c d e : A) :
    (fun i => f (![a,b,c,d,e] i))=![f a,f b,f c,f d,f e] := by
  funext i
  fin_cases i <;> rfl

private theorem frame_ambient {G : Type*} [Group G] (P₁ B P₂ : Subgroup G)
    (h₁ : B≤P₁) (h₂ : B≤P₂)
    (F : Frame (RankTwoAmalgam.ofSubgroups P₁ B P₂ h₁ h₂)) :
    ∃ k d z t q : G,
      k∈B ∧ orderOf k=3 ∧ d∈P₂ ∧ orderOf d=3 ∧ z∈B ∧ orderOf z=2 ∧
      z∈twoCore P₂ ∧ (∀ a∈twoCore P₂,z*a=a*z) ∧
      q∈B ∧ orderOf q=4 ∧ q∈⁅twoCore P₁,zpowers k⁆ ∧
      t∈P₁ ∧ t^2=1 ∧ t∉B ∧ t*k*t⁻¹=k⁻¹ ∧ d*k=k*d ∧
      d⁻¹*z*d∈B ∧ (d*t)⁻¹*z*(d*t)∈B ∧ d⁻¹*q*d∈B ∧
      closure (Set.range ![k,t,q,d⁻¹*q*d])=P₁ ∧
      closure (Set.range ![k,d,z,(d*t)⁻¹*z*(d*t),q])=P₂ := by
  let k : G := F.k
  let d : G := F.d
  let z : G := F.z
  let t : G := F.t
  let q : G := F.q
  have hu : (F.u:G)=d⁻¹*z*d := congrArg Subtype.val F.u_relation
  have hv : (F.v:G)=t⁻¹*(F.u:G)*t := congrArg Subtype.val F.v_relation
  have hw : (F.w:G)=d⁻¹*q*d := congrArg Subtype.val F.w_relation
  have hv' : (F.v:G)=(d*t)⁻¹*z*(d*t) := by rw [hv,hu]; group
  have hleft : closure (Set.range ![k,t,q,d⁻¹*q*d])=P₁ := by
    have hh := ambient_generate P₁ _ F.left_generate
    rw [map_vec4] at hh
    change closure (Set.range ![k,t,q,(F.w:G)])=_ at hh
    rwa [hw] at hh
  have hright : closure (Set.range ![k,d,z,(d*t)⁻¹*z*(d*t),q])=P₂ := by
    have hh := ambient_generate P₂ _ F.right_generate
    rw [map_vec5] at hh
    change closure (Set.range ![k,d,z,(F.v:G),q])=_ at hh
    rwa [hv'] at hh
  have hz : z∈twoCore P₂ := mem_map_of_mem P₂.subtype F.z_core
  have hzc : ∀ a∈twoCore P₂,z*a=a*z := by
    rintro _ ⟨a,ha,rfl⟩
    exact congrArg Subtype.val (F.z_central a ha)
  have hq : q∈⁅twoCore P₁,zpowers k⁆ := by
    have hh := mem_map_of_mem P₁.subtype F.q_commutator
    rw [map_commutator,MonoidHom.map_zpowers] at hh
    exact hh
  have htB : t∉B := by
    intro ht
    exact F.t_outside ⟨⟨t,ht⟩,Subtype.ext rfl⟩
  exact ⟨k,d,z,t,q,F.k.property,(orderOf_coe F.k).trans F.k_order,
    F.d.property,(orderOf_coe F.d).trans F.d_order,
    F.z.property,(orderOf_coe F.z).trans F.z_order,hz,hzc,
    F.q.property,(orderOf_coe F.q).trans F.q_order,hq,F.t.property,
    congrArg Subtype.val F.t_square,htB,congrArg Subtype.val F.t_inverts,
    congrArg Subtype.val F.d_commutes,hu ▸ F.u.property,hv' ▸ F.v.property,
    hw ▸ F.w.property,hleft,hright⟩

open SuzukiContainment GreenBook
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The exact reduced endpoint words and both original full-Borel
supplements, for either orientation of a compatible reduced J₂ comparison. -/
public theorem original_endpoint_generators
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam) :
    ∃ k d z t q : G,
      k∈commonBorel L (reducedSylow L S) ∧ orderOf k=3 ∧
      d∈parabolic L (reducedSylow L S) j ∧ orderOf d=3 ∧
      z∈commonBorel L (reducedSylow L S) ∧ orderOf z=2 ∧
      z∈twoCore (parabolic L S j) ∧
      (∀ a∈twoCore (parabolic L S j),z*a=a*z) ∧
      q∈commonBorel L (reducedSylow L S) ∧ orderOf q=4 ∧
      q∈⁅twoCore (parabolic L S i),zpowers k⁆ ∧
      t∈parabolic L (reducedSylow L S) i ∧ t^2=1 ∧ t∉commonBorel L S ∧
      t*k*t⁻¹=k⁻¹ ∧ d*k=k*d ∧
      d⁻¹*z*d∈commonBorel L (reducedSylow L S) ∧
      (d*t)⁻¹*z*(d*t)∈commonBorel L (reducedSylow L S) ∧
      d⁻¹*q*d∈commonBorel L (reducedSylow L S) ∧
      closure (Set.range ![k,t,q,d⁻¹*q*d])=parabolic L (reducedSylow L S) i ∧
      closure (Set.range ![k,d,z,(d*t)⁻¹*z*(d*t),q])=parabolic L (reducedSylow L S) j ∧
      closure (Set.range ![k,t,q,d⁻¹*q*d]) ⊔ commonBorel L S=parabolic L S i ∧
      closure (Set.range ![k,d,z,(d*t)⁻¹*z*(d*t),q]) ⊔ commonBorel L S=parabolic L S j := by
  obtain ⟨F₀⟩ := model_frame
  obtain ⟨k,d,z,t,q,hk,hko,hd,hdo,hz,hzo,hzQ,hzc,hq,hqo,hqQ,ht,ht2,htB,htk,hdk,hu,hv,hw,hleft,hright⟩ :=
    frame_ambient _ _ _ (commonBorel_le_parabolic i) (commonBorel_le_parabolic j) (F₀.map e.symm)
  rw [reduced_parabolic_core h j] at hzQ hzc
  rw [reduced_parabolic_core h i] at hqQ
  have htB' : t∉commonBorel L S := by
    intro hh
    apply htB
    rw [←reduced_parabolic_inf_borel h i]
    exact ⟨ht,hh⟩
  refine ⟨k,d,z,t,q,hk,hko,hd,hdo,hz,hzo,hzQ,hzc,hq,hqo,hqQ,ht,ht2,htB',htk,hdk,hu,hv,hw,hleft,hright,?_,?_⟩
  · rw [hleft]
    exact reduced_parabolic_supplement h i
  · rw [hright]
    exact reduced_parabolic_supplement h j

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.GeneratorRelations
