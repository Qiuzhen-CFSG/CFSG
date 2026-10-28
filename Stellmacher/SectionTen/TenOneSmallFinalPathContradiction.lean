module
public import Stellmacher.SectionTen.TenOneSmallCentralizerElementary
public import Stellmacher.SectionTen.TenOneCenterPointCentralizerType
public import Theory.GroupTheory.InvolutionPairCentralInvolution

public import Stellmacher.SectionTen.TenOneSmallEightPath
public import Stellmacher.SectionTen.TenOneSmallEightPathCenterObstruction

/-!
# The final small-case contradiction from centralizer and fusion control

In the actual small Section Ten context, the three local assertions used
at the end of (10.1)(a3) are incompatible: full ambient centralizers of
Wstar points outside Zmiddle lie in the mapped middle stabilizer; an
ambient conjugate of the terminal center commuting with such a point
lies in Zmiddle; and every native involution outside Zmiddle in its local
centralizer can be conjugated into Wstar outside Zmiddle. These three
assertions are explicit premises here. The final nonsolvable-centralizer
assembly supplies their proved producers under its contrary assumption.

Choose a point a of elementary Wstar outside the middle four-center and
an involution b generating the far center on an actual nonbacktracking
eight-edge walk. Fusion excludes their conjugacy. The finite dihedral
lemma gives an involution v in their generated subgroup commuting with
both. Centralizer containment puts v in the middle stabilizer; the proved
path-center obstruction rules out v in the middle center. Native reduction
conjugates v into Wstar. Conjugate a and b by the same actor. Fusion puts
the new b in the elementary middle center, and centralizer containment
makes the new a normalize that center. The actual product decomposition
of the center with the cyclic involution shows that a central v outside
the center forces a and b to commute. Pulling this equality back, fusion
puts the original far center inside the middle center, contradicting the
same path obstruction. No quotient by a nonnormal subgroup is used.

Source: Stellmacher (10.1)(a3), Journal of Algebra190 (1997), printed p.62
after (11). The graph, critical path and embedding remain unchanged; all
three elements are transported together by one native group conjugation.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped Pointwise
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G→*H} {T A B : Subgroup G}

omit [Finite H] in
private theorem ambient_line_class_of_isConj (K:Subgroup H) (x y:H)
    (hx:∃g:H,K.map (MulAut.conj g).toMonoidHom=zpowers x)
    (hxy:IsConj x y) : ∃g:H,K.map (MulAut.conj g).toMonoidHom=zpowers y := by
  obtain ⟨h,hh⟩ := hx
  obtain ⟨g,rfl⟩ := isConj_iff.mp hxy
  refine ⟨g*h,?_⟩
  have hcomp : (MulAut.conj (g*h)).toMonoidHom=
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom := by
    ext z
    simp [mul_assoc]
  rw [hcomp,←Subgroup.map_map,hh,MonoidHom.map_zpowers]
  rfl

private theorem orbit_center_ambient_line_class
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (vertex:ctx.Γ.Vertex)
    (horbit:IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex)
    (point:G) (hgen:ZAt ctx.Γ vertex=zpowers point) :
    ∃g:H,((ZAt ctx.Γ ctx.criticalPath.a').map embedding).map
      (MulAut.conj g).toMonoidHom=zpowers (embedding point) := by
  let Γ := ctx.Γ
  obtain ⟨s,hs⟩ := horbit
  obtain ⟨t,_,ht⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ ctx.criticalPath ctx.commutator_eq
  let mover := t⁻¹*s
  have hmove : Γ.act mover ctx.criticalPath.a'=vertex := by
    have hc : Γ.act t⁻¹ ctx.criticalPath.a'=ctx.criticalPath.firstStep := by
      rw [←ht,←Γ.act_mul,mul_inv_cancel,Γ.act_one]
    dsimp only [mover]
    rw [Γ.act_mul,hc,hs]
  have hmap : (ZAt Γ ctx.criticalPath.a').map (MulAut.conj mover⁻¹).toMonoidHom=
      ZAt Γ vertex := by
    change (z Γ ctx.criticalPath.a').map (MulAut.conj mover⁻¹).toMonoidHom=z Γ vertex
    rw [←z_act,hmove]
  refine ⟨embedding mover⁻¹,?_⟩
  have hcomp : (MulAut.conj (embedding mover⁻¹)).toMonoidHom.comp embedding=
      embedding.comp (MulAut.conj mover⁻¹).toMonoidHom := by
    ext x
    simp
  rw [Subgroup.map_map,hcomp,←Subgroup.map_map,hmap,hgen,MonoidHom.map_zpowers]

private theorem pair_commute_of_central_involution_outside
    (Z:Subgroup G) [IsMulCommutative Z] (a b u:G)
    (ha:orderOf a=2) (haN:a∈normalizer (Z:Set G)) (hb:b∈Z)
    (hu:u∈zpowers a⊔zpowers b) (huZ:u∉Z) (hub:Commute u b) : Commute a b := by
  classical
  have hsmall : zpowers a⊔zpowers b≤Z⊔zpowers a :=
    sup_le le_sup_right ((zpowers_le.mpr hb).trans le_sup_left)
  have hprod : u∈(Z:Set G)*(zpowers a:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Z (zpowers a) (zpowers_le.mpr haN)]
    exact hsmall hu
  obtain ⟨z,hz,k,hk,hprod⟩ := hprod
  have hkcases : k=1∨k=a := by
    change k∈zpowers a at hk
    rw [mem_zpowers_iff_mem_range_orderOf,ha] at hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    have hnlt : n<2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  rcases hkcases with hkone | hka
  · have hueq : z=u := by simpa only [hkone,mul_one] using hprod
    exact (huZ (hueq ▸ hz)).elim
  · rw [hka] at hprod
    change z*a=u at hprod
    have hzb : Commute z b := setLike_mul_comm (s:=Z) hz hb
    have hleft : z*(a*b)=z*(b*a) := by
      calc
        z*(a*b) = (z*a)*b := (mul_assoc _ _ _).symm
        _ = u*b := by rw [hprod]
        _ = b*u := hub.eq
        _ = b*(z*a) := by rw [hprod]
        _ = (b*z)*a := (mul_assoc _ _ _).symm
        _ = (z*b)*a := by rw [hzb.eq]
        _ = z*(b*a) := mul_assoc _ _ _
    exact mul_left_cancel hleft

public theorem ten_one_small_final_path_contradiction
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0:Set G)
    (∀a:G,a∈Wstar→a∉ZAt ctx.Γ middle→
      Subgroup.centralizer ({embedding a}:Set H)≤(GAt ctx.Γ middle).map embedding) →
    (∀a v:G,a∈Wstar→a∉ZAt ctx.Γ middle→Commute a v→
      (∃g:H,((ZAt ctx.Γ ctx.criticalPath.a').map embedding).map
        (MulAut.conj g).toMonoidHom=zpowers (embedding v))→v∈ZAt ctx.Γ middle) →
    (∀a v:G,a∈Wstar→a∉ZAt ctx.Γ middle→ orderOf v=2→v∈GAt ctx.Γ middle→
      Commute a v→v∉ZAt ctx.Γ middle→
      ∃g:G,MulAut.conj g v∈Wstar ∧ MulAut.conj g v∉ZAt ctx.Γ middle) → False := by
  dsimp only
  intro hcontain hfusion hreduce
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Z := ZAt Γ middle
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓ GeneratedNeighborhoodV Γ middle
  let Wstar := QAt Γ middle ⊓ Subgroup.centralizer (W0:Set G)
  let K := (ZAt Γ cp.a').map embedding
  have hshort : 1<cp.length := by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  have hstructure := ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  change GAt Γ middle≤normalizer (Wstar:Set G) ∧
    IsElementaryAbelian 2 Wstar ∧ (Nat.card Wstar=8∨Nat.card Wstar=16) ∧
    Wstar⊓twoCoreIn (EAt Γ middle)=Z ∧ ⁅Wstar,EAt Γ middle⁆≤Z at hstructure
  let _ : IsElementaryAbelian 2 Wstar := hstructure.2.1
  have hZcard : Nat.card Z=4 := (sectionTenOpeningData ctx middle hpath).center_card
  let _ : IsElementaryAbelian 2 Z := by
    change IsElementaryAbelian 2 (ZAt ctx.Γ middle)
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  have hWnot : ¬Wstar≤Z := by
    intro hle
    have hc := card_le_of_le hle
    rw [hZcard] at hc
    rcases hstructure.2.2.1 with hh | hh <;> rw [hh] at hc <;> omega
  obtain ⟨a,haW,haZ⟩ := SetLike.not_le_iff_exists.mp hWnot
  have hane : a≠1 := by intro heq; exact haZ (heq ▸ Z.one_mem)
  have ha2 : orderOf a=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Wstar) a haW) hane
  have hnative (x v:G) (hx:x∈Wstar) (hxZ:x∉Z) (hcomm:Commute x v) : v∈GAt Γ middle := by
    have hh := hcontain x hx hxZ
      (mem_centralizer_singleton_iff.mpr (show embedding v*embedding x=embedding x*embedding v from
        by simpa only [map_mul] using congrArg embedding hcomm.symm.eq))
    obtain ⟨w,hw,heq⟩ := hh
    exact (ctx.embedding_injective heq) ▸ hw
  obtain ⟨path,h0,h1,_,hadj,hback⟩ := ten_one_small_exists_eight_path ctx middle hpath hmodel
  have hgeometry := ten_one_small_eight_path_center_obstruction ctx hsmall hmodel path h0 hadj hback
  have hnoncomm (neighbor:Γ.Vertex) (hn:Γ.adjacent middle neighbor) :
      ⁅ZAt Γ neighbor,ZAt Γ (path 8)⁆≠⊥ := by
    apply hgeometry.1 neighbor
    rwa [h1]
  have hnotB : ¬ZAt Γ (path 8)≤Z := by
    change ¬ZAt Γ (path 8)≤ZAt Γ middle
    simpa only [h1] using hgeometry.2
  let localCtx := ctx.toLocalContext.toSectionNineLocalContext
  have horbit0 : IsConjugateVertex Γ cp.firstStep (path 0) := by
    rw [h0]
    exact ⟨1,Γ.act_one _⟩
  have horbit2 := goldschmidt_orbit_step localCtx horbit0 (Γ.adjacent_symm (hadj 0)) (hadj 1)
  have horbit4 := goldschmidt_orbit_step localCtx horbit2 (Γ.adjacent_symm (hadj 2)) (hadj 3)
  have horbit6 := goldschmidt_orbit_step localCtx horbit4 (Γ.adjacent_symm (hadj 4)) (hadj 5)
  have horbit8 := goldschmidt_orbit_step localCtx horbit6 (Γ.adjacent_symm (hadj 6)) (hadj 7)
  have hBcard : Nat.card (ZAt Γ (path 8))=2 :=
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
      (path 8) horbit8).1
  have hBne : ¬ZAt Γ (path 8)≤⊥ := by
    intro hle
    have heq := le_antisymm hle bot_le
    rw [heq] at hBcard
    simp at hBcard
  obtain ⟨b,hbB,hbne⟩ := SetLike.not_le_iff_exists.mp hBne
  change b≠1 at hbne
  have hbpow : b^2=1 := by
    have hh := pow_card_eq_one' (x:=(⟨b,hbB⟩:ZAt Γ (path 8)))
    rw [hBcard] at hh
    exact congrArg Subtype.val hh
  have hb2 : orderOf b=2 := orderOf_eq_prime hbpow hbne
  have hBgen : ZAt Γ (path 8)=zpowers b := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hbB)
    rw [hBcard,Nat.card_zpowers,hb2]
  have hbClass : ∃g:H,K.map (MulAut.conj g).toMonoidHom=zpowers (embedding b) :=
    orbit_center_ambient_line_class ctx (path 8) horbit8 b hBgen
  have hnotConj : ¬IsConj a b := by
    intro hab
    have haClass := ambient_line_class_of_isConj K (embedding b) (embedding a) hbClass
      (embedding.map_isConj hab.symm)
    exact haZ (hfusion a a haW haZ (Commute.refl a) haClass)
  obtain ⟨v,hvGen,hv2,hva,hvb⟩ :=
    Theory.GroupTheory.exists_central_involution_of_not_isConj a b ha2 hb2 hnotConj
  have hvne : v≠1 := by intro heq; simp [heq] at hv2
  have hvP : v∈GAt Γ middle := hnative a v haW haZ hva.symm
  have hvZ : v∉Z := by
    intro hz
    obtain ⟨neighbor,hn,hline⟩ := ten_one_center_point_neighbor ctx middle hpath v hz hvne
    apply hnoncomm neighbor hn
    rw [hline,hBgen,commutator_eq_bot_iff_le_centralizer]
    apply zpowers_le.mpr
    rw [zpowers_eq_closure,centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hvb.eq
  obtain ⟨g,hgW,hgZ⟩ := hreduce a v haW haZ hv2 hvP hva.symm hvZ
  let e := MulAut.conj g
  have hea2 : orderOf (e a)=2 := (e.orderOf_eq a).trans ha2
  have hevGen : e v∈zpowers (e a)⊔zpowers (e b) := by
    have hh := mem_map_of_mem e.toMonoidHom hvGen
    rwa [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hh
  have hevb : Commute (e v) (e b) := hvb.map e.toMonoidHom
  have heva : Commute (e v) (e a) := hva.map e.toMonoidHom
  have hebClass : ∃h:H,K.map (MulAut.conj h).toMonoidHom=zpowers (embedding (e b)) := by
    apply ambient_line_class_of_isConj K (embedding b) (embedding (e b)) hbClass
    apply embedding.map_isConj
    exact isConj_iff.mpr ⟨g,rfl⟩
  have hebZ : e b∈Z := hfusion (e v) (e b) hgW hgZ hevb hebClass
  have heaP : e a∈GAt Γ middle := hnative (e v) (e a) hgW hgZ heva
  have heaN : e a∈normalizer (Z:Set G) := stabilizer_le_normalizer_z Γ middle heaP
  have heab : Commute (e a) (e b) := pair_commute_of_central_involution_outside
    Z (e a) (e b) (e v) hea2 heaN hebZ hevGen hgZ hevb
  have hab : Commute a b := by
    apply e.injective
    simpa only [map_mul] using heab.eq
  have hbZ : b∈Z := hfusion a b haW haZ hab hbClass
  apply hnotB
  rw [hBgen]
  exact zpowers_le.mpr hbZ

end Stellmacher.SectionTen
