module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoFrameActors

/-!
# The quaternion word for the same original Hall–Janko frame

The checked cubic orbit contains every order-four element of the moved
quaternion factor. The original norm theorem supplies an order-eight product
for one such element. Conjugating the outer involution by the corresponding
power of k gives the order-eight product with the frame's own q. This keeps
its d- and z-actions and its inversion of k. The same involution complements
the full original Borel and both original endpoint extensions.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–230.
The reduced comparison retains both inclusion squares. No order-twelve
lift or original Aut(J₂) recognition is inferred here.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open SuzukiContainment GreenBook GeneratorRelations
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem conjugation_fixed {A : Type*} [Group A]
    (c a : A) (hc : Commute c a) : MulAut.conj c⁻¹ a=a := by
  change c⁻¹*a*(c⁻¹)⁻¹=a
  rw [hc.inv_left.eq,mul_inv_cancel_right]

private theorem involution_product_inverse_order {A : Type*} [Group A]
    (x q : A) (hx : x^2=1) : orderOf (x*q⁻¹)=orderOf (x*q) := by
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hh := (MulAut.conj x).orderOf_eq (q⁻¹*x)
  have he : MulAut.conj x (q⁻¹*x)=x*q⁻¹ := by
    change x*(q⁻¹*x)*x⁻¹=x*q⁻¹
    group
  rw [he] at hh
  calc
    orderOf (x*q⁻¹)=orderOf (q⁻¹*x) := hh
    _ = orderOf ((x*q)⁻¹) := by rw [mul_inv_rev,hxi]
    _ = orderOf (x*q) := orderOf_inv _

private theorem rotate_outer {A : Type*} [Group A]
    (B N : Subgroup A) (_hNB : N≤B) (k x : B) (d z q : A)
    (hkN : (k:A)∈N) (hx : x^2=1) (hxN : (x:A)∉N)
    (hxk : x*k*x⁻¹=k⁻¹) (hkd : (k:A)*d=d*(k:A))
    (hkz : (k:A)*z=z*(k:A)) (hxd : (x:A)*d=d*(x:A))
    (hxz : (x:A)*z=z*(x:A)) (n : ℕ)
    (ho : orderOf ((x:A)*((k:A)^n*q*((k:A)^n)⁻¹))=8 ∨
      orderOf ((x:A)*((k:A)^n*q⁻¹*((k:A)^n)⁻¹))=8) :
    ∃ y : B,y^2=1 ∧ (y:A)∉N ∧ y*k*y⁻¹=k⁻¹ ∧
      (y:A)*d=d*(y:A) ∧ (y:A)*z=z*(y:A) ∧ orderOf ((y:A)*q)=8 := by
  let c : B := k^n
  let a : MulAut B := MulAut.conj c⁻¹
  let b : MulAut A := MulAut.conj ((c:A)⁻¹)
  let y : B := a x
  have hak : a k=k := conjugation_fixed c k ((Commute.refl k).pow_left n)
  have hbk : b (k:A)=(k:A) := conjugation_fixed (c:A) (k:A)
    ((Commute.refl (k:A)).pow_left n)
  have hbd : b d=d := conjugation_fixed (c:A) d ((show Commute (k:A) d from hkd).pow_left n)
  have hbz : b z=z := conjugation_fixed (c:A) z ((show Commute (k:A) z from hkz).pow_left n)
  have hby : b (x:A)=(y:A) := rfl
  have hy2 : y^2=1 := by
    change (a x)^2=1
    rw [←map_pow,hx,map_one]
  have hyN : (y:A)∉N := by
    intro hy
    have hcN : (c:A)∈N := N.pow_mem hkN n
    have hh := N.mul_mem (N.mul_mem hcN hy) (N.inv_mem hcN)
    apply hxN
    convert hh using 1
    change _= (c:A)*((c:A)⁻¹*(x:A)*((c:A)⁻¹)⁻¹)*(c:A)⁻¹
    group
  have hyk : y*k*y⁻¹=k⁻¹ := by
    simpa only [map_mul,map_inv,hak] using congrArg a hxk
  have hyd : (y:A)*d=d*(y:A) := by
    simpa only [map_mul,hby,hbd] using congrArg b hxd
  have hyz : (y:A)*z=z*(y:A) := by
    simpa only [map_mul,hby,hbz] using congrArg b hxz
  have hord (w : A) : orderOf ((y:A)*w)=
      orderOf ((x:A)*((k:A)^n*w*((k:A)^n)⁻¹)) := by
    have hh := b.orderOf_eq ((x:A)*((k:A)^n*w*((k:A)^n)⁻¹))
    have he : b ((x:A)*((k:A)^n*w*((k:A)^n)⁻¹))=(y:A)*w := by
      change (c:A)⁻¹*((x:A)*((c:A)*w*(c:A)⁻¹))*((c:A)⁻¹)⁻¹=
        ((c:A)⁻¹*(x:A)*((c:A)⁻¹)⁻¹)*w
      group
    rwa [he] at hh
  refine ⟨y,hy2,hyN,hyk,hyd,hyz,?_⟩
  rcases ho with ho | ho
  · exact (hord q).trans ho
  · rw [←involution_product_inverse_order (y:A) q (congrArg (fun y : B => (y:A)) hy2)]
    exact (hord q⁻¹).trans ho

private theorem frame_word_orbit {A : Type*} [Group A]
    (R B P Q : Subgroup A) (hBR : B≤R) (hBP : B≤P) (he : twoCore R=Q)
    (F : Frame (RankTwoAmalgam.ofSubgroups R B P hBR hBP)) (hF : F.QuaternionOrbit)
    (x : A)
    (hex : ∃ y : A,y∈⁅Q,zpowers (F.k:A)⁆ ∧ orderOf y=4 ∧ orderOf (x*y)=8) :
    ∃ n : Fin 3,
      orderOf (x*((F.k:A)^n.val*(F.q:A)*((F.k:A)^n.val)⁻¹))=8 ∨
      orderOf (x*((F.k:A)^n.val*(F.q:A)⁻¹*((F.k:A)^n.val)⁻¹))=8 := by
  obtain ⟨y,hy,ho,hxy⟩ := hex
  let kR := inclusion hBR F.k
  have hm : (⁅pCore 2 R,zpowers kR⁆).map R.subtype=⁅Q,zpowers (F.k:A)⁆ := by
    rw [map_commutator,MonoidHom.map_zpowers]
    change ⁅twoCore R,zpowers (F.k:A)⁆=_
    rw [he]
  rw [←hm] at hy
  obtain ⟨a,ha,rfl⟩ := hy
  obtain ⟨n,hn⟩ := hF a ha ((orderOf_coe a).symm.trans ho)
  refine ⟨n,?_⟩
  rcases hn with hn | hn
  · have hh := congrArg (fun y : R => (y:A)) hn
    change (a:A)=(F.k:A)^n.val*(F.q:A)*((F.k:A)^n.val)⁻¹ at hh
    exact Or.inl (hh ▸ hxy)
  · have hh := congrArg (fun y : R => (y:A)) hn
    change (a:A)=(F.k:A)^n.val*(F.q:A)⁻¹*((F.k:A)^n.val)⁻¹ at hh
    exact Or.inr (hh ▸ hxy)

private theorem frame_product_orbit_of_word {A : Type*} [Group A]
    (R B₀ P B Q : Subgroup A) (hR : B₀≤R) (hP : B₀≤P) (hB : B₀≤B)
    (he : twoCore R=Q) (F : Frame (RankTwoAmalgam.ofSubgroups R B₀ P hR hP))
    (hF : F.QuaternionOrbit) (x : B)
    (hxk : (x:A)*(F.k:A)*(x:A)⁻¹=(F.k:A)⁻¹)
    (hword : ∀ k : B,orderOf k=3 → x*k*x⁻¹=k⁻¹ →
      ∃ y : A,y∈⁅Q,zpowers (k:A)⁆ ∧ orderOf y=4 ∧ orderOf ((x:A)*y)=8) :
    ∃ n : Fin 3,
      orderOf ((x:A)*((F.k:A)^n.val*(F.q:A)*((F.k:A)^n.val)⁻¹))=8 ∨
      orderOf ((x:A)*((F.k:A)^n.val*(F.q:A)⁻¹*((F.k:A)^n.val)⁻¹))=8 := by
  let kB := inclusion hB F.k
  have hkB : orderOf kB=3 := (orderOf_injective
    (inclusion hB) (inclusion_injective _) F.k).trans F.k_order
  have hinv : x*kB*x⁻¹=kB⁻¹ := Subtype.ext hxk
  exact frame_word_orbit R B₀ P Q hR hP he F hF (x:A) (hword kB hkB hinv)

private theorem frame_product_orbit
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (hF : F.QuaternionOrbit) (x : commonBorel L S) (hx : x^2=1)
    (hxk : (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹) :
    ∃ n : Fin 3,
      orderOf ((x:G)*((F.k:G)^n.val*(F.q:G)*((F.k:G)^n.val)⁻¹))=8 ∨
      orderOf ((x:G)*((F.k:G)^n.val*(F.q:G)⁻¹*((F.k:G)^n.val)⁻¹))=8 := by
  exact frame_product_orbit_of_word _ _ _ _ _
    (commonBorel_le_parabolic i) (commonBorel_le_parabolic j) (reduced_commonBorel_le h)
    (reduced_parabolic_core h i) F hF x hxk
    (fun k hk hinv => original_quaternion_word h i e k x hk hx hinv)

private theorem rotate_frame {A : Type*} [Group A]
    (P₁ B₀ P₂ B : Subgroup A) (h₁ : B₀≤P₁) (h₂ : B₀≤P₂) (hB : B₀≤B)
    (F : Frame (RankTwoAmalgam.ofSubgroups P₁ B₀ P₂ h₁ h₂))
    (hkz : F.k*F.z=F.z*F.k) (x : B) (hx : x^2=1) (hxN : (x:A)∉B₀)
    (hxk : (x:A)*(F.k:A)*(x:A)⁻¹=(F.k:A)⁻¹)
    (hxd : (x:A)*(F.d:A)=(F.d:A)*(x:A))
    (hxz : (x:A)*(F.z:A)=(F.z:A)*(x:A))
    (ho : ∃ n : Fin 3,
      orderOf ((x:A)*((F.k:A)^n.val*(F.q:A)*((F.k:A)^n.val)⁻¹))=8 ∨
      orderOf ((x:A)*((F.k:A)^n.val*(F.q:A)⁻¹*((F.k:A)^n.val)⁻¹))=8) :
    ∃ y : B,y^2=1 ∧ (y:A)∉B₀ ∧
      (y:A)*(F.k:A)*(y:A)⁻¹=(F.k:A)⁻¹ ∧
      (y:A)*(F.d:A)=(F.d:A)*(y:A) ∧
      (y:A)*(F.z:A)=(F.z:A)*(y:A) ∧ orderOf ((y:A)*(F.q:A))=8 := by
  obtain ⟨n,hn⟩ := ho
  let kB := inclusion hB F.k
  have hinv : x*kB*x⁻¹=kB⁻¹ := Subtype.ext hxk
  obtain ⟨y,hy,hyN,hyk,hyd,hyz,hyq⟩ := rotate_outer B B₀ hB
    kB x (F.d:A) (F.z:A) (F.q:A) F.k.property hx hxN hinv
    (congrArg Subtype.val F.d_commutes).symm (congrArg Subtype.val hkz) hxd hxz n.val hn
  exact ⟨y,hy,hyN,congrArg Subtype.val hyk,hyd,hyz,hyq⟩

/-- The source quaternion relation is satisfied by the q in the same
endpoint frame: no second existential choice of q is substituted. -/
public theorem original_aligned_quaternion_frame
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
      IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
        (zpowers x) ∧
      ∀ r : Fin 2, IsComplement'
        ((parabolic L (reducedSylow L S) r).subgroupOf (parabolic L S r))
        (zpowers (inclusion (commonBorel_le_parabolic r) x)) := by
  obtain ⟨F,x,hd,hkz,hF,hx,hxN,hxk,hxd,hxz⟩ := original_aligned_frame h i j e hne
  have ho := frame_product_orbit h i j e.left F hF x hx hxk
  obtain ⟨y,hy,hyN,hyk,hyd,hyz,hyq⟩ := rotate_frame
    _ _ _ _ (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)
    (reduced_commonBorel_le h) F hkz x hx hxN hxk hxd hxz ho
  exact ⟨F,y,hd,hkz,hy,hyN,hyk,hyd,hyz,hyq,
    original_outer_borel_complement h i e.left hne y hy hyN,
    original_outer_endpoint_complement h i e.left hne y hy hyN⟩

/-- Obtain the quaternion relation while retaining the specified frame. -/
public theorem original_quaternion_actor_for_frame
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S)
    (F : Frame (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)))
    (hkz : F.k*F.z=F.z*F.k) (hF : F.QuaternionOrbit)
    (x : commonBorel L S) (hx : x^2=1)
    (hxN : (x:G)∉commonBorel L (reducedSylow L S))
    (hxk : (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹)
    (hxd : (x:G)*(F.d:G)=(F.d:G)*(x:G))
    (hxz : (x:G)*(F.z:G)=(F.z:G)*(x:G)) :
      ∃ x : commonBorel L S,
      x^2=1 ∧ (x:G)∉commonBorel L (reducedSylow L S) ∧
      (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ ∧
      (x:G)*(F.d:G)=(F.d:G)*(x:G) ∧
      (x:G)*(F.z:G)=(F.z:G)*(x:G) ∧ orderOf ((x:G)*(F.q:G))=8 ∧
      IsComplement' ((commonBorel L (reducedSylow L S)).subgroupOf (commonBorel L S))
        (zpowers x) ∧
      ∀ r : Fin 2, IsComplement'
        ((parabolic L (reducedSylow L S) r).subgroupOf (parabolic L S r))
        (zpowers (inclusion (commonBorel_le_parabolic r) x)) := by
  have ho := frame_product_orbit h i j e.left F hF x hx hxk
  obtain ⟨y,hy,hyN,hyk,hyd,hyz,hyq⟩ := rotate_frame
    _ _ _ _ (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)
    (reduced_commonBorel_le h) F hkz x hx hxN hxk hxd hxz ho
  exact ⟨y,hy,hyN,hyk,hyd,hyz,hyq,
    original_outer_borel_complement h i e.left hne y hy hyN,
    original_outer_endpoint_complement h i e.left hne y hy hyN⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
