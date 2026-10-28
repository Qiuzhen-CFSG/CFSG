module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoFrameProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoActionLift

/-!
# Order twelve for the same original Hall–Janko generator frame

The marked concrete frame retains its Cartan, cubic, central involution and
inverter coordinates through both reduced inclusion squares. The original
normalizer construction and quaternion orbit then align one outer involution
with this particular frame. Compatible conjugation on the two endpoints forces
(xt)⁶=z. The replacement t↦tk preserves this identity because xt commutes with
k and k³=1, so the literal quotient-order-six choice has order twelve before
quotienting. Both endpoint generating sets and all original complements remain.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231.
The finite paired-action calculation substitutes for the printed quaternion
centralizer calculation. Genuine compatible reduced recognition is still an
input; marked original Aut(J₂) recognition is not inferred from these orders.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open SuzukiContainment GreenBook GeneratorRelations ProductLift
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer GeneratorPair GeneratorPair.SecondOrbitCertificate

private theorem canonical_model_frame :
    ∃ F : Frame HallJanko.j2Model.toMarking.amalgam,
      F.d=catalogueIso.right sourceCubic ∧
      F.k=catalogueIso.middle sourceCartan ∧
      F.z=catalogueIso.middle sourceCentral ∧
      F.t=catalogueIso.left sourceInverter ∧
      F.k*F.z=F.z*F.k ∧
      QuotientGroup.mk' (pCore 2 (HallJanko.j2Model.toMarking.P 1))
        (HallJanko.j2Model.toMarking.amalgam.right F.k) ∈
          center (HallJanko.j2Model.toMarking.P 1 ⧸ pCore 2 (HallJanko.j2Model.toMarking.P 1)) ∧
      F.QuaternionOrbit := by
  obtain ⟨F,hd,hkz,hkc,hF,hk,hz,ht⟩ := model_frame_coordinates
  obtain ⟨ck,cd,cz,ct⟩ := source_coordinates
  refine ⟨F,?_,?_,?_,?_,hkz,hkc,hF⟩
  · apply Subtype.ext
    exact (congrArg (fun a : HallJanko.j2Model.toMarking.P 1 => (a:Carrier)) hd).trans cd.symm
  · exact Subtype.ext (hk.trans ck.symm)
  · exact Subtype.ext (hz.trans cz.symm)
  · exact Subtype.ext (ht.trans ct.symm)

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem canonical_reduced_frame
    (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam) :
    ∃ F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      F.d=reducedCubic j e.right ∧
      F.d=e.right.symm (catalogueIso.right sourceCubic) ∧
      F.k=e.middle.symm (catalogueIso.middle sourceCartan) ∧
      F.z=e.middle.symm (catalogueIso.middle sourceCentral) ∧
      F.t=e.left.symm (catalogueIso.left sourceInverter) ∧
      F.k*F.z=F.z*F.k ∧
      QuotientGroup.mk' (pCore 2 (parabolic L (reducedSylow L S) j))
        (inclusion (commonBorel_le_parabolic j) F.k) ∈
          center (parabolic L (reducedSylow L S) j ⧸ pCore 2 (parabolic L (reducedSylow L S) j)) ∧
      F.QuaternionOrbit := by
  obtain ⟨F,hd,hk,hz,ht,hkz,hkc,hF⟩ := canonical_model_frame
  refine ⟨F.map e.symm,?_,?_,?_,?_,?_,?_,?_,F.quaternionOrbit_map e.symm hF⟩
  · rw [Frame.map_d,hd]
    apply congrArg e.right.symm
    apply Subtype.ext
    exact source_coordinates.2.1
  · rw [Frame.map_d,hd]; rfl
  · rw [Frame.map_k,hk]; rfl
  · rw [Frame.map_z,hz]; rfl
  · rw [Frame.map_t,ht]; rfl
  · rw [Frame.map_k,Frame.map_z]
    exact (map_mul e.middle.symm _ _).symm.trans
      ((congrArg e.middle.symm hkz).trans (map_mul e.middle.symm _ _))
  · let v := LocalCoreTransport.quotientEquiv 2 e.right.symm
    have hh := (Subgroup.centerCongr v ⟨_,hkc⟩).property
    change QuotientGroup.mk' _ (e.symm.right
      (HallJanko.j2Model.toMarking.amalgam.right F.k)) ∈ _ at hh
    rw [e.symm.right_commutes] at hh
    rw [Frame.map_k]
    exact hh

private theorem sixth_twist {A : Type*} [Group A] (x t k : A)
    (hk : k^3=1) (hxk : x*k*x⁻¹=k⁻¹) (htk : t*k*t⁻¹=k⁻¹) :
    (x*(t*k))^6=(x*t)^6 := by
  have he : (x*t)*k*(x*t)⁻¹=k := by
    calc
      (x*t)*k*(x*t)⁻¹=x*(t*k*t⁻¹)*x⁻¹ := by group
      _=x*k⁻¹*x⁻¹ := by rw [htk]
      _=(x*k*x⁻¹)⁻¹ := by group
      _=k := by rw [hxk,inv_inv]
  have hc : Commute (x*t) k := mul_inv_eq_iff_eq_mul.mp he
  have hk6 : k^6=1 := by rw [show (6:ℕ)=3*2 from rfl,pow_mul,hk,one_pow]
  rw [←mul_assoc,hc.mul_pow,hk6,mul_one]

private theorem frame_order_twelve
    (h : HypothesisF11 L S) (i j : Fin 2)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
      (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
      (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (x : commonBorel L S) (h6 : orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
      (inclusion (commonBorel_le_parabolic i) x*inclusion (reduced_parabolic_le h i) F.t))=6)
    (hs : ((x:G)*(F.t:G))^6=(F.z:G)) : orderOf ((x:G)*(F.t:G))=12 := by
  apply order_twelve_of_sixth _ (F.z:G) ((orderOf_coe F.z).trans F.z_order) hs
  let a : parabolic L S i := inclusion (commonBorel_le_parabolic i) x*
    inclusion (reduced_parabolic_le h i) F.t
  have hd := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 (parabolic L S i))) a
  rw [show orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i)) a)=6 from h6] at hd
  exact (orderOf_coe a).symm ▸ hd

/-- One source frame and one actual outer involution have both product orders,
with the full original Borel and both original endpoint complements retained. -/
public theorem original_aligned_frame_product_twelve
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S) :
    ∃ F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)),
      ∃ x : commonBorel L S,
      F.d=reducedCubic j e.right ∧ F.k*F.z=F.z*F.k ∧
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ ∧
      (x:G)*(F.d:G)=(F.d:G)*(x:G) ∧
      (x:G)*(F.z:G)=(F.z:G)*(x:G) ∧ orderOf ((x:G)*(F.q:G))=8 ∧
      orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
        (inclusion (commonBorel_le_parabolic i) x*
          inclusion (reduced_parabolic_le h i) F.t))=6 ∧
      ((x:G)*(F.t:G))^6=(F.z:G) ∧ orderOf ((x:G)*(F.t:G))=12 ∧
      IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
        (zpowers x) ∧
      ∀ r : Fin 2, IsComplement'
        ((parabolic L (reducedSylow L S) r).subgroupOf (parabolic L S r))
        (zpowers (inclusion (commonBorel_le_parabolic r) x)) := by
  obtain ⟨F,hd,hcd,hck,hcz,hct,hkz,hkc,hF⟩ := canonical_reduced_frame i j e
  obtain ⟨x,hx,hxN,hxk,hxd,hxz⟩ := original_actor_for_marked_frame h i j e hne F hd hkc
  obtain ⟨y,hy,hyN,hyk,hyd,hyz,hyq,hB,hP⟩ :=
    original_quaternion_actor_for_frame h i j e hne F hkz hF x hx hxN hxk hxd hxz
  let f := e.trans catalogueIso.symm
  have hs : ((y:G)*(F.t:G))^6=(F.z:G) := by
    rw [hct,hcz]
    apply original_product_sixth h i j f y hy
    · exact hck ▸ hyk
    · exact hcd ▸ hyd
    · exact hcz ▸ hyz
  obtain ⟨F',hchoice,hk',hd',hz',hq',h6⟩ :=
    original_frame_product_six_choice h i j e.left hne F y hyN hyk
  have hs' : ((y:G)*(F'.t:G))^6=(F'.z:G) := by
    rcases hchoice with rfl | rfl
    · exact hs
    · rw [Frame.twistT_t,Frame.twistT_z]
      change ((y:G)*((F.t:G)*(F.k:G)))^6=(F.z:G)
      have htinv := congrArg (fun a : parabolic L (reducedSylow L S) i => (a:G)) F.t_inverts
      have hh : F.k^3=1 := by rw [←F.k_order,pow_orderOf_eq_one]
      have hk3 := congrArg (fun a : commonBorel L (reducedSylow L S) => (a:G)) hh
      exact (sixth_twist _ _ _ hk3 hyk htinv).trans hs
  refine ⟨F',y,hd'.trans hd,?_,hy,hyN,?_,?_,?_,?_,h6,hs',
    frame_order_twelve h i j F' y h6 hs',hB,hP⟩
  · rwa [hk',hz']
  · rwa [hk']
  · rwa [hd']
  · rwa [hz']
  · rwa [hq']

/-- One original complement and one concrete outer-Borel involution induce
exactly the same actions on both whole reduced endpoints and their common Borel.
No action premise is added to the compatible reduced recognition input. -/
public theorem original_aligned_action_lift
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S) :
    let e₀ := e.trans catalogueIso.symm
    ∃ x : commonBorel L S, ∃ y : SecondParabolic.Overlap.outerB,
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      y^2=1 ∧ (y:Extension)∉intoExtension.range ∧
      (∀ b : commonBorel L (reducedSylow L S),
        (e₀.middle ((commonBorel L (reducedSylow L S)).normalizerMonoidHom
          ⟨(x:G),borel_normalizes_reduced h x.property⟩ b):Carrier)=
          extensionAction y (e₀.middle b:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) i,
        (e₀.left (reducedEndpointAction h i x v):Carrier)=extensionAction y (e₀.left v:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) j,
        (e₀.right (reducedEndpointAction h j x v):Carrier)=extensionAction y (e₀.right v:Carrier)) ∧
      IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
        (zpowers x) ∧
      ∀ r : Fin 2, IsComplement'
        ((parabolic L (reducedSylow L S) r).subgroupOf (parabolic L S r))
        (zpowers (inclusion (commonBorel_le_parabolic r) x)) := by
  obtain ⟨F,hd,hcd,hck,hcz,_,_,hkc,_⟩ := canonical_reduced_frame i j e
  obtain ⟨x,hx,hxN,hxk,hxd,hxz⟩ := original_actor_for_marked_frame h i j e hne F hd hkc
  let e₀ := e.trans catalogueIso.symm
  obtain ⟨y,hy,hyN,hB,hL,hR⟩ := original_actor_lift h i j e₀ x
    (hck ▸ hxk) (hcd ▸ hxd) (hcz ▸ hxz)
  exact ⟨x,y,hx,hxN,hy,hyN,hB,hL,hR,
    original_outer_borel_complement h i e.left hne x hx hxN,
    original_outer_endpoint_complement h i e.left hne x hx hxN⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
