module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.DiagonalCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PlaneFusion

/-!
# The strongly three-embedded branch of G₂(3) recognition

Suppose the original cubic plane is ambient Sylow. A diagonal cubic has
Sylow two-subgroups of order two in its centralizer: a larger two-subgroup,
a central involution, and involution fusion would put the cubic in a factor
class, contrary to the proved plane fusion. The centralizer has a normal odd
complement. The marked Klein four and the involution-centralizer orders
force that complement to be a three-group, hence the original plane of
order nine. Thus the diagonal centralizer is precisely the plane times the
marked central involution, of order eighteen.

Both factor centralizers already lie in H in this branch. Burnside fusion
now shows that every conjugator between cubics of H lies in H. Therefore
H meets each conjugate by an element outside H in a subgroup of order prime
to three. The last theorem gives every clause of strong three-embedding
from the original configuration and the small Sylow-order branch.

This proves the reduction to the exceptional strongly three-embedded case
in the source discussion of Aschbacher–Smith I.4.5, printed p.417,
refs/quasithin.pdf, PDF p.428. It does not exclude that case: the cited
Janko, J. Algebra 12 (1969), pp.360–371, and Aschbacher, J. Algebra 257
(2002), pp.197–214, contain the further recognition arguments. The actual
Atlas equivalence also remains open. Chapter14SylowNine applies these
calculations to the literal SourceLocalData without assuming their conclusions.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
namespace CubicTorus
variable {c} (t : CubicTorus c)

include c in
private theorem odd_fixed_card_dvd_nine (D : Subgroup G) (hD : Odd (Nat.card D))
    (v : G) (hv : orderOf v=2) :
    Nat.card (D ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G) ∣ 9 := by
  let F := D ⊓ Subgroup.centralizer ({v}:Set G)
  have ho : Odd (Nat.card F) := hD.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hd : Nat.card F ∣ 64*9 := by
    have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
    rwa [involution_centralizer_card c v hv] at hh
  exact (ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd

private theorem plane_subgroup_oddCore_card_dvd (K : Subgroup G)
    (hK : K ≤ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer (K:Set G))) ∣ 3^6 := by
  let C := Subgroup.centralizer (K:Set G)
  let D := (pPrimeCore 2 C).map C.subtype
  have hDcard : Nat.card D=Nat.card (pPrimeCore 2 C) := card_map_of_injective C.subtype_injective
  have hD : Odd (Nat.card D) := by
    rw [hDcard]
    exact Nat.Coprime.odd_of_left pPrimeCore_coprime_card
  have hTN : t.torus.map c.H.subtype ≤ normalizer (D:Set G) :=
    (t.torus_normalizes_plane_subgroup K hK).trans
      ((normalizer_le_normalizer_centralizer K).trans
        (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)))
  have hzT : (t.z:G)∈t.torus.map c.H.subtype := mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers _))
  have hnT : (t.n:G)∈t.torus.map c.H.subtype := mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers _))
  let a : normalizer (D:Set G) := ⟨t.z,hTN hzT⟩
  let b : normalizer (D:Set G) := ⟨t.n,hTN hnT⟩
  have ha : a^2=1 := Subtype.ext (by
    change (t.z:G)^2=1
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G))
  have hb : b^2=1 := Subtype.ext (by
    change (t.n:G)^2=1
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G))
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  have hzn : t.z≠t.n := by
    intro he
    apply t.outside
    rw [←he]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)
  have hab2 : orderOf ((a*b:normalizer (D:Set G)):G)=2 := by
    have hp : (((a*b:normalizer (D:Set G)):G))^2=1 := by
      have hh := hab.mul_pow 2
      rw [ha,hb,one_mul] at hh
      exact congrArg Subtype.val hh
    have hne : (((a*b:normalizer (D:Set G)):G))≠1 := by
      intro hh
      have hni : (t.n:G)⁻¹=(t.n:G) := inv_eq_of_mul_eq_one_left
        (by simpa only [orderOf_coe,t.n_order,pow_two] using pow_orderOf_eq_one (t.n:G))
      exact hzn (Subtype.ext ((eq_inv_of_mul_eq_one_left hh).trans hni))
    exact orderOf_eq_prime hp hne
  have hformula := D.card_three_odd_centralizers hD a b ha hb hab
  have hd : Nat.card D ∣
      Nat.card (D ⊓ Subgroup.centralizer ({(a:G)}:Set G) : Subgroup G) *
      Nat.card (D ⊓ Subgroup.centralizer ({(b:G)}:Set G) : Subgroup G) *
      Nat.card (D ⊓ Subgroup.centralizer ({((a*b:normalizer (D:Set G)):G)}:Set G) : Subgroup G) := by
    rw [←hformula]
    exact dvd_mul_right _ _
  have hx := odd_fixed_card_dvd_nine (c:=c) D hD (t.z:G) ((orderOf_coe t.z).trans t.z_order)
  have hy := odd_fixed_card_dvd_nine (c:=c) D hD (t.n:G) ((orderOf_coe t.n).trans t.n_order)
  have hz := odd_fixed_card_dvd_nine (c:=c) D hD ((a*b:normalizer (D:Set G)):G) hab2
  have hbig := hd.trans (Nat.mul_dvd_mul (Nat.mul_dvd_mul hx hy) hz)
  change Nat.card (pPrimeCore 2 C) ∣ 3^6
  rwa [hDcard] at hbig

private theorem diagonal_sylow_two_card
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u : G) (hu : orderOf u=3)
    (huE : u∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hux : u∉zpowers ((t.x:c.H):G)) (huy : u∉zpowers ((t.y:c.H):G))
    (P : Sylow 2 (Subgroup.centralizer ({u}:Set G))) : Nat.card P=2 := by
  let C := Subgroup.centralizer ({u}:Set G)
  have hEH : zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) ≤ c.H :=
    sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property)
  have hzC : (t.z:G)∈C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ hEH huE)).symm
  have htwo : 2∣Nat.card C := by
    have hd := orderOf_dvd_natCard (⟨t.z,hzC⟩:C)
    have ho : orderOf (⟨t.z,hzC⟩:C)=2 := (orderOf_coe (⟨t.z,hzC⟩:C)).symm.trans
      ((orderOf_coe t.z).trans t.z_order)
    exact ho ▸ hd
  have hPtwo : 2∣Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n:=1) (by simpa using htwo)
  have hnotfour : ¬4∣Nat.card P := by
    intro hfour
    have hfourle : 4≤Nat.card P := Nat.le_of_dvd Nat.card_pos hfour
    let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
    obtain ⟨n,hn,hncard⟩ := (P.isPGroup'.to_subgroup (center P)).nontrivial_iff_card.mp inferInstance
    obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=center P) 2
      (hncard ▸ dvd_pow_self 2 hn.ne')
    let vG : G := (((v:P):C):G)
    have hvG : orderOf vG=2 := by
      dsimp only [vG]
      rw [orderOf_coe,orderOf_coe,orderOf_coe,hv]
    obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_conjugate c vG (t.z:G) hvG
      ((orderOf_coe t.z).trans t.z_order))
    change MulAut.conj g vG=(t.z:G) at hg
    let f : P →* G := (MulAut.conj g).toMonoidHom.comp
      (C.subtype.comp (P:Subgroup C).subtype)
    have hf : Function.Injective f := (MulAut.conj g).injective.comp
      (C.subtype_injective.comp (P:Subgroup C).subtype_injective)
    have hfH (p : P) : f p∈c.H := by
      rw [t.centralizer]
      apply mem_centralizer_singleton_iff.mpr
      have hvp : ((p:C):G)*vG=vG*((p:C):G) :=
        congrArg (fun w : P => ((w:C):G)) (mem_center_iff.mp v.property p)
      have hh := congrArg (MulAut.conj g) hvp
      change MulAut.conj g (((p:C):G))*(t.z:G)=(t.z:G)*MulAut.conj g (((p:C):G))
      simpa only [map_mul,hg] using hh
    have huH : MulAut.conj g u∈c.H := by
      rw [t.centralizer]
      apply mem_centralizer_singleton_iff.mpr
      have huv : u*vG=vG*u := (mem_centralizer_singleton_iff.mp ((v:P):C).property).symm
      have hh := congrArg (MulAut.conj g) huv
      change MulAut.conj g u*(t.z:G)=(t.z:G)*MulAut.conj g u
      simpa only [map_mul,hg] using hh
    let uH : c.H := ⟨MulAut.conj g u,huH⟩
    let fH : P →* c.H := f.codRestrict c.H hfH
    have hfC (p : P) : fH p ∈ Subgroup.centralizer ({uH}:Set c.H) := by
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      change MulAut.conj g (((p:C):G))*MulAut.conj g u =
        MulAut.conj g u*MulAut.conj g (((p:C):G))
      simpa only [map_mul] using congrArg (MulAut.conj g)
        (mem_centralizer_singleton_iff.mp (p:C).property)
    let fC := fH.codRestrict (Subgroup.centralizer ({uH}:Set c.H)) hfC
    have hdiv : Nat.card P ∣ Nat.card (Subgroup.centralizer ({uH}:Set c.H)) :=
      card_dvd_of_injective fC (fun a b he => hf
        (congrArg (fun w : Subgroup.centralizer ({uH}:Set c.H) => ((w:c.H):G)) he))
    have hu3 : orderOf uH=3 := (orderOf_coe uH).symm.trans
      (((MulAut.conj g).orderOf_eq u).trans hu)
    obtain ⟨h,hh⟩ := t.local_cubic_four_dvd_forces_factor uH hu3 (hfour.trans hdiv)
    have hmap : (zpowers u).map (MulAut.conj (h*g)).toMonoidHom =
        (zpowers (uH:G)).map (MulAut.conj h).toMonoidHom := by
      rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers]
      congr 1
      change (h*g)*u*(h*g)⁻¹=h*(g*u*g⁻¹)*h⁻¹
      group
    rcases hh with hh|hh
    · have he := t.plane_subgroup_eq_of_conjugate_of_sylow hS
        (zpowers u) (zpowers ((t.x:c.H):G)) (zpowers_le.mpr huE) le_sup_left
        (h*g) (hmap.trans hh)
      exact hux (he ▸ mem_zpowers u)
    · have he := t.plane_subgroup_eq_of_conjugate_of_sylow hS
        (zpowers u) (zpowers ((t.y:c.H):G)) (zpowers_le.mpr huE) le_sup_right
        (h*g) (hmap.trans hh)
      exact huy (he ▸ mem_zpowers u)
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hnlt : n<2 := by
    by_contra he
    apply hnotfour
    rw [hn]
    exact pow_dvd_pow 2 (by omega : 2≤n)
  interval_cases n
  · rw [hn] at hPtwo
    norm_num at hPtwo
  · exact hn

/-- In the Sylow-nine branch a diagonal cubic has centralizer of order18. -/
theorem diagonal_centralizer_card_of_sylow
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u : G) (hu : orderOf u=3)
    (huE : u∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hux : u∉zpowers ((t.x:c.H):G)) (huy : u∉zpowers ((t.y:c.H):G)) :
    Nat.card (Subgroup.centralizer ({u}:Set G))=18 := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let C := Subgroup.centralizer ({u}:Set G)
  let O := pPrimeCore 2 C
  let P : Sylow 2 C := default
  have hP := t.diagonal_sylow_two_card hS u hu huE hux huy P
  have heven : 2∣Nat.card C := hP ▸ (P:Subgroup C).card_subgroup_dvd_card
  have hprod := (P.isComplement'_pPrimeCore_of_isCyclic (isCyclic_of_prime_card hP) heven).card_mul_card
  change Nat.card P*Nat.card O=Nat.card C at hprod
  rw [hP] at hprod
  have hO : Nat.card O ∣ 3^6 := by
    have hh := t.plane_subgroup_oddCore_card_dvd (zpowers u) (zpowers_le.mpr huE)
    rwa [zpowers_eq_closure,centralizer_closure] at hh
  have hpO : IsPGroup 3 O := IsPGroup.of_card_dvd_pow hO
  obtain ⟨S,hS⟩ := hS
  have hSc : Nat.card S=9 := by
    rw [hS]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  obtain ⟨R,hOR⟩ := (hpO.map C.subtype).exists_le_sylow
  have hle : Nat.card O≤9 := by
    have hh := card_le_of_le hOR
    rw [card_map_of_injective C.subtype_injective] at hh
    have hR : Nat.card R=9 := (Nat.card_congr (R.equiv S).toEquiv).trans hSc
    exact hh.trans hR.le
  have hEC : E≤C := by
    let : IsElementaryAbelian 3 E := (cubic_plane_data c t.x t.y t.x_order t.y_order).1
    intro e he
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨e,he⟩:E) ⟨u,huE⟩))
  have h9 : 9∣Nat.card C := by
    have hh := card_dvd_of_le hEC
    rwa [(cubic_plane_data c t.x t.y t.x_order t.y_order).2] at hh
  rw [←hprod] at h9
  have h9O : 9∣Nat.card O := (by decide : Nat.Coprime 9 2).dvd_of_dvd_mul_left h9
  have hge := Nat.le_of_dvd (Nat.card_pos (α:=O)) h9O
  have hOc : Nat.card O=9 := by omega
  exact hprod.symm.trans (by rw [hOc])

/-- The full diagonal centralizer is the original plane times the marked
central involution. In particular it lies in the original H. -/
theorem diagonal_centralizer_of_sylow
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u : G) (hu : orderOf u=3)
    (huE : u∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hux : u∉zpowers ((t.x:c.H):G)) (huy : u∉zpowers ((t.y:c.H):G)) :
    Subgroup.centralizer ({u}:Set G)=
      (zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) ⊔ zpowers (t.z:G) := by
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  have hEH : E≤c.H := sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property)
  let : IsElementaryAbelian 3 E := (cubic_plane_data c t.x t.y t.x_order t.y_order).1
  have hEC : E≤Subgroup.centralizer ({u}:Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨e,he⟩:E) ⟨u,huE⟩))
  have hzC : zpowers (t.z:G)≤Subgroup.centralizer ({u}:Set G) := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (t.centralizer ▸ hEH huE)).symm)
  have hzE : zpowers (t.z:G)≤Subgroup.centralizer (E:Set G) := by
    apply zpowers_le.mpr
    intro e he
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ hEH he)
  have hcard : Nat.card (E ⊔ zpowers (t.z:G) : Subgroup G)=18 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint E (zpowers (t.z:G))
      (hzE.trans (Subgroup.centralizer_le_normalizer _))
      (disjoint_of_coprime_natCard (by
        rw [(cubic_plane_data c t.x t.y t.x_order t.y_order).2,
          Nat.card_zpowers,orderOf_coe,t.z_order]; decide)),
      (cubic_plane_data c t.x t.y t.x_order t.y_order).2,
      Nat.card_zpowers,orderOf_coe,t.z_order]
  exact (eq_of_le_of_card_ge (sup_le hEC hzC) (by
    rw [hcard,t.diagonal_centralizer_card_of_sylow hS u hu huE hux huy])).symm

/-- All cubic centralizers in the original plane lie in H when the plane
is ambient Sylow. This includes both original factors and both diagonals. -/
theorem plane_cubic_centralizer_le_H_of_sylow
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u : G) (hu : orderOf u=3)
    (huE : u∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    Subgroup.centralizer ({u}:Set G)≤c.H := by
  have hs := t.cubic_plane_sylow_iff.mp hS
  have factor {d : G2ThreeConfiguration G} (x : d.H₁) (hx : orderOf x=3)
      (hcore : Nat.card (cubicOddCore d x)=3) (hum : u∈zpowers ((x:d.H):G)) :
      Subgroup.centralizer ({u}:Set G)≤d.H := by
    have he : zpowers u=zpowers ((x:d.H):G) := eq_of_le_of_card_ge (zpowers_le.mpr hum)
      (by rw [Nat.card_zpowers,Nat.card_zpowers,hu,orderOf_coe,orderOf_coe,hx])
    have hC : Subgroup.centralizer ({u}:Set G)≤normalizer (zpowers u:Set G) := by
      rw [←centralizer_closure,←zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    rw [he] at hC
    exact hC.trans ((cubic_normalizer_le_H_iff d x hx).mpr hcore)
  by_cases hx : u∈zpowers ((t.x:c.H):G)
  · exact factor t.x t.x_order hs.1 hx
  by_cases hy : u∈zpowers ((t.y:c.H):G)
  · exact factor (d:=swapFactors c) t.y t.y_order hs.2 hy
  rw [t.diagonal_centralizer_of_sylow hS u hu huE hx hy]
  exact sup_le (sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property))
    (zpowers_le.mpr t.z.property)

private theorem conjugator_mem_of_plane_cubics
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u v g : G) (hu : orderOf u=3)
    (huE : u∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hvE : v∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hg : MulAut.conj g u=v) : g∈c.H := by
  obtain ⟨h,hh,hhe⟩ := t.plane_fusion_in_H_of_sylow hS u v huE hvE
    (isConj_iff.mpr ⟨g,hg⟩)
  have hC : h⁻¹*g∈Subgroup.centralizer ({u}:Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      _ = h⁻¹*(g*u*g⁻¹)*h := by group
      _ = h⁻¹*v*h := by rw [show g*u*g⁻¹=v from hg]
      _ = u := by rw [←hhe]; simp [MulAut.conj_apply,mul_assoc]
  have hmem := c.H.mul_mem hh ((t.plane_cubic_centralizer_le_H_of_sylow hS u hu huE) hC)
  simpa only [←mul_assoc,mul_inv_cancel,one_mul] using hmem

/-- Every cubic line of the original plane has its full ambient normalizer
inside H in the Sylow-nine branch. -/
theorem plane_cubic_normalizer_le_H_of_sylow
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u : G) (hu : orderOf u=3)
    (huE : u∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    normalizer (zpowers u:Set G)≤c.H := by
  intro g hg
  have hgu : MulAut.conj g u∈zpowers u := (hg u).mp (mem_zpowers u)
  exact t.conjugator_mem_of_plane_cubics hS u (MulAut.conj g u) g hu huE
    ((zpowers_le.mpr huE) hgu) rfl

private theorem cubic_H_conjugate_into_plane (u : c.H) (hu : orderOf u=3) :
    ∃ h : c.H, MulAut.conj (h:G) (u:G)∈
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
  let B : Subgroup c.H := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hmap : B.map c.H.subtype=zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hB : Nat.card B=9 := by
    rw [←card_map_of_injective c.H.subtype_injective,hmap]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hi : B.index=64 := by
    have hh := B.card_mul_index
    rw [hB,H_card c] at hh
    omega
  let P : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hB).toSylow
    (by rw [hi]; decide)
  obtain ⟨b,hb⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n:=1) (by simpa using hu)
  obtain ⟨h,hh⟩ := isConj_iff.mp hb
  refine ⟨h,?_⟩
  have he : MulAut.conj (h:G) (u:G)=((b:c.H):G) := congrArg Subtype.val hh
  rw [he,←hmap]
  exact mem_map_of_mem _ b.property

/-- No ambient conjugator between cubic elements of H can leave H in
the Sylow-nine branch. -/
theorem cubic_conjugator_mem_H_of_sylow
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (u v : c.H) (hu : orderOf u=3) (g : G)
    (hg : MulAut.conj g (u:G)=(v:G)) : g∈c.H := by
  have hv : orderOf v=3 := by
    have he := (MulAut.conj g).orderOf_eq (u:G)
    rw [hg,orderOf_coe,orderOf_coe,hu] at he
    exact he
  obtain ⟨a,ha⟩ := t.cubic_H_conjugate_into_plane u hu
  obtain ⟨b,hb⟩ := t.cubic_H_conjugate_into_plane v hv
  have hconj : MulAut.conj ((b:G)*g*(a:G)⁻¹) (MulAut.conj (a:G) (u:G))=
      MulAut.conj (b:G) (v:G) := by
    change ((b:G)*g*(a:G)⁻¹)*((a:G)*(u:G)*(a:G)⁻¹)*((b:G)*g*(a:G)⁻¹)⁻¹=
      (b:G)*(v:G)*(b:G)⁻¹
    calc
      _ = (b:G)*(g*(u:G)*g⁻¹)*(b:G)⁻¹ := by group
      _ = _ := by rw [show g*(u:G)*g⁻¹=(v:G) from hg]
  have hm := t.conjugator_mem_of_plane_cubics hS _ _ _
    (((MulAut.conj (a:G)).orderOf_eq (u:G)).trans ((orderOf_coe u).trans hu)) ha hb hconj
  have hprod := c.H.mul_mem (c.H.mul_mem (c.H.inv_mem b.property) hm) a.property
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hprod

/-- In the Sylow-nine branch H is strongly three-embedded: every distinct
conjugate meets it in a subgroup of order prime to three. The original
ambient conjugation convention is explicit. -/
theorem H_intersection_conjugate_three_prime_of_sylow
    (hS : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (g : G) (hg : g∉c.H) :
    ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  intro hd
  let I := c.H ⊓ c.H.map (MulAut.conj g).toMonoidHom
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G:=I) 3 hd
  obtain ⟨v,hv,hvu⟩ := u.property.2
  let uH : c.H := ⟨u,u.property.1⟩
  let vH : c.H := ⟨v,hv⟩
  have hv3 : orderOf vH=3 := by
    have he := (MulAut.conj g).orderOf_eq v
    change MulAut.conj g v=(u:G) at hvu
    rw [hvu,orderOf_coe,hu] at he
    exact (orderOf_coe vH).symm.trans he.symm
  exact hg (t.cubic_conjugator_mem_H_of_sylow hS vH uH hv3 g hvu)

include t in
/-- The small Sylow branch gives the properness, divisibility, and conjugate
intersection clauses of strong three-embedding for the original H. -/
theorem H_strongly_three_embedded_of_not_cube_dvd (hsmall : ¬3^3∣Nat.card G) :
    c.H≠⊤ ∧ 3∣Nat.card c.H ∧
      ∀ g : G, g∉c.H →
        ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  have hS := t.cubic_plane_sylow_iff.mpr (t.small_cores_iff_not_cube_dvd.mpr hsmall)
  refine ⟨?_,?_,t.H_intersection_conjugate_three_prime_of_sylow hS⟩
  · intro he
    apply H_sup_oddCore_ne_top c
    rw [he,top_sup_eq]
  · rw [H_card c]
    decide

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
