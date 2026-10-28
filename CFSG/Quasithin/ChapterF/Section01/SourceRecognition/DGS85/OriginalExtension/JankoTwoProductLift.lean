module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoProductLiftModel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action


/-!
# Lifting the Hall–Janko product to order twelve in the original endpoint

Conjugation by the original full Borel gives compatible actions on both
literal reduced endpoints. The checked paired-action relation transports
through the two inclusion squares and gives (xt)⁶ equal to the marked
central involution. Its nontriviality, together with order six in the
original first two-core quotient, gives order twelve in the original group.

The actor equations refer to the designated reduced Cartan, cubic and
central element. Their simultaneous choice and the reduced comparison
remain explicit inputs. This theorem neither strengthens ParabolicModel
nor constructs the full Aut(J₂) comparison.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.230–231.
The subgroup transport is kept abstract so the kernel need not repeatedly
normalize the original quotient and core inclusion expressions.
-/


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.ProductLift
open SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem ambient_product_sixth
    (P B R : Subgroup G) (hP : B≤P) (hR : B≤R)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B R hP hR) modelAmalgam)
    (x : G) (hx : x^2=1)
    (hxP : x∈normalizer (P:Set G)) (hxB : x∈normalizer (B:Set G))
    (hxR : x∈normalizer (R:Set G))
    (hk : x*(e.middle.symm sourceCartan:G)*x⁻¹=(e.middle.symm sourceCartan:G)⁻¹)
    (hd : x*(e.right.symm sourceCubic:G)=(e.right.symm sourceCubic:G)*x)
    (hz : x*(e.middle.symm sourceCentral:G)=(e.middle.symm sourceCentral:G)*x) :
    (x*(e.left.symm sourceInverter:G))^6=(e.middle.symm sourceCentral:G) := by
  let b : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P B R hP hR)
      (RankTwoAmalgam.ofSubgroups P B R hP hR) := {
    left := P.normalizerMonoidHom ⟨x,hxP⟩
    middle := B.normalizerMonoidHom
      ⟨x,hxB⟩
    right := R.normalizerMonoidHom ⟨x,hxR⟩
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
  let a := (e.symm.trans b).trans e
  have hk' : a.middle sourceCartan=sourceCartan⁻¹ := by
    apply e.middle.symm.injective
    change e.middle.symm (e.middle (b.middle (e.middle.symm sourceCartan)))=_
    rw [e.middle.symm_apply_apply,map_inv]
    exact Subtype.ext hk
  have hd' : a.right sourceCubic=sourceCubic := by
    apply e.right.symm.injective
    change e.right.symm (e.right (b.right (e.right.symm sourceCubic)))=_
    rw [e.right.symm_apply_apply]
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hd)
  have hz' : a.middle sourceCentral=sourceCentral := by
    apply e.middle.symm.injective
    change e.middle.symm (e.middle (b.middle (e.middle.symm sourceCentral)))=_
    rw [e.middle.symm_apply_apply]
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hz)
  have hh := congrArg e.left.symm (model_actor_sixth a hk' hd' hz')
  rw [map_pow,map_mul] at hh
  have hzleft : e.left.symm (modelAmalgam.left sourceCentral)=
      inclusion hP (e.middle.symm sourceCentral) :=
    e.symm.left_commutes sourceCentral
  rw [hzleft] at hh
  have he : e.left.symm (a.left sourceInverter)=b.left (e.left.symm sourceInverter) :=
    e.left.symm_apply_apply _
  rw [he] at hh
  have hhG := congrArg (fun y : P => (y:G)) hh
  change ((x*(e.left.symm sourceInverter:G)*x⁻¹)*(e.left.symm sourceInverter:G))^3=
    (e.middle.symm sourceCentral:G) at hhG
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  rw [hxi] at hhG
  have heq : (x*(e.left.symm sourceInverter:G)*x)*(e.left.symm sourceInverter:G)=
      (x*(e.left.symm sourceInverter:G))^2 := by simp only [pow_two,mul_assoc]
  rwa [heq,←pow_mul] at hhG

public theorem original_product_sixth
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)) modelAmalgam)
    (x : commonBorel L S) (hx : x^2=1)
    (hk : (x:G)*(e.middle.symm sourceCartan:G)*(x:G)⁻¹=(e.middle.symm sourceCartan:G)⁻¹)
    (hd : (x:G)*(e.right.symm sourceCubic:G)=(e.right.symm sourceCubic:G)*(x:G))
    (hz : (x:G)*(e.middle.symm sourceCentral:G)=(e.middle.symm sourceCentral:G)*(x:G)) :
    ((x:G)*(e.left.symm sourceInverter:G))^6=(e.middle.symm sourceCentral:G) := by
  apply ambient_product_sixth _ _ _ (commonBorel_le_parabolic i)
    (commonBorel_le_parabolic j) e (x:G)
    (congrArg (fun y : commonBorel L S => (y:G)) hx)
    (parabolic_normalizes_reduced h i (commonBorel_le_parabolic i x.property))
    (borel_normalizes_reduced h x.property)
    (parabolic_normalizes_reduced h j (commonBorel_le_parabolic j x.property)) hk hd hz

/-- A central involution as sixth power and the quotient divisibility determine order twelve. -/
public theorem order_twelve_of_sixth {A : Type*} [Group A]
    (a z : A) (hz : orderOf z=2)
    (ha : a^6=z) (h6 : 6∣orderOf a) : orderOf a=12 := by
  have hz2 : z^2=1 := by rw [←hz,pow_orderOf_eq_one]
  have ha12 : a^12=1 := by
    rw [show (12:ℕ)=6*2 from rfl,pow_mul,ha,hz2]
  have hdiv : orderOf a∣12 := orderOf_dvd_of_pow_eq_one ha12
  have hpos : 0<orderOf a := Nat.pos_of_dvd_of_pos hdiv (by decide)
  have hle : orderOf a≤12 := Nat.le_of_dvd (by decide) hdiv
  have hne : orderOf a≠6 := by
    intro he
    have hh : z=1 := ha.symm.trans (he ▸ pow_orderOf_eq_one a)
    rw [hh,orderOf_one] at hz
    omega
  obtain ⟨n,hn⟩ := h6
  omega

private theorem subgroup_product_order_twelve (P B R : Subgroup G)
    (hB : B≤P) (hR : R≤P) (x : B) (t : R) (z : G)
    (hz : orderOf z=2) (hs : ((x:G)*(t:G))^6=z)
    (h6 : orderOf (QuotientGroup.mk' (pCore 2 P) (inclusion hB x*inclusion hR t))=6) :
    orderOf ((x:G)*(t:G))=12 := by
  apply order_twelve_of_sixth _ z hz hs
  let a : P := inclusion hB x*inclusion hR t
  have hd := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 P)) a
  rw [show orderOf (QuotientGroup.mk' (pCore 2 P) a)=6 from h6] at hd
  exact (orderOf_coe a).symm ▸ hd

/-- The sixth-power identity lifts order six from the literal original
first two-core quotient to order twelve in the original endpoint. -/
public theorem original_product_twelve
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j)) modelAmalgam)
    (x : commonBorel L S) (hx : x^2=1)
    (hk : (x:G)*(e.middle.symm sourceCartan:G)*(x:G)⁻¹=(e.middle.symm sourceCartan:G)⁻¹)
    (hd : (x:G)*(e.right.symm sourceCubic:G)=(e.right.symm sourceCubic:G)*(x:G))
    (hz : (x:G)*(e.middle.symm sourceCentral:G)=(e.middle.symm sourceCentral:G)*(x:G))
    (h6 : orderOf (QuotientGroup.mk' (pCore 2 (parabolic L S i))
      (inclusion (commonBorel_le_parabolic i) x*
        inclusion (reduced_parabolic_le h i) (e.left.symm sourceInverter)))=6) :
    orderOf ((x:G)*(e.left.symm sourceInverter:G))=12 := by
  apply subgroup_product_order_twelve (parabolic L S i) _ _
    (commonBorel_le_parabolic i) (reduced_parabolic_le h i) x (e.left.symm sourceInverter)
    (e.middle.symm sourceCentral:G) _ (original_product_sixth h i j e x hx hk hd hz) h6
  exact (orderOf_coe (e.middle.symm sourceCentral)).trans
    ((e.middle.symm.orderOf_eq sourceCentral).trans sourceCentral_order)



end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.ProductLift
