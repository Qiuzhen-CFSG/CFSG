module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SixCycle.Orbit
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.BaseDegree
public import Theory.Combinatorics.SimpleGraph.SixCycle.Recognition
/-!
# Six actual source parabolics in cyclic order

Start with F1 and its two uniquely labeled neighbors Eu,Ezu. The genuine
second reflection gives Et=t⁻¹F1, fixes both u-colored members, and has
Et different from Ezu. The quaternion reflection fixes F1 and interchanges
its two neighbors. Pair alignment puts Eu in the base orbit, so its neighbor
set also has cardinality two; hence t⁻¹ swaps F1 and Et.

The six vertices F1,Eu,Et,t⁻¹Ezu,rEt,Ezu are pairwise distinct with colors
z,u,zu,z,u,zu. Translating the original edges gives the six cycle edges.
Every vertex has an explicit conjugator in the original plane normalizer.
Both original fixed fives and nextFive retain their specified positions.
Source: Aschbacher--Smith J.4.10, printed pp.444--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.SixCycle
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
open ChapterF.SourceCompletion.BinaryRee
@[expose] def colorWord {G:Type*} [Group G] (z u:G) : Fin 6→G := ![z,u,z*u,z,u,z*u]
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include q s hi f hleft hz hfive

theorem source_cycle_coordinates :
    ∃v:Fin 6→ globalFamily p B5 c.z (sourceU e),
      Function.Injective v ∧ v 0=baseVertex p B5 c e hz ∧
      (∀i,(v i:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (colorWord c.z (sourceU e) i)) ∧
      (∀i,(sourceGraph p B5 c.z (sourceU e)).Adj (v i) (v (i+1))) ∧
      (∀i,∃n:G,n∈normalizer (pairSpan c.z (sourceU e):Set G) ∧
        (p.F₁ B5).conjBy n=(v i:Subgroup G)) ∧
      fixedFive B5 (sourceU e)≤v 1 ∧ fixedFive B5 (c.z*sourceU e)≤v 5 ∧
      nextFive c B5 (sourceU e)≤v 2 := by
  let X:=globalFamily p B5 c.z (sourceU e)
  let Γ:=sourceGraph p B5 c.z (sourceU e)
  let x:X:=baseVertex p B5 c e hz
  let N:=normalizer (pairSpan c.z (sourceU e):Set G)
  obtain ⟨Eu,Ezu,hEu,hEzu,hBu,hBzu,hune,hbase⟩ :=
    source_base_neighbors_iff q p s c B5 hi e f hleft hz hfive
  have hxy:Γ.Adj x Eu:=(hbase Eu).mpr (Or.inl rfl)
  have hxw:Γ.Adj x Ezu:=(hbase Ezu).mpr (Or.inr rfl)
  have hcard0:Nat.card (Γ.neighborSet x)=2 := by
    have he:Γ.neighborSet x={Eu,Ezu}:=Set.ext fun E=>hbase E
    rw [he,Nat.card_coe_set_eq,Set.ncard_pair hune]
  obtain ⟨g,hg,hgEu⟩ := labeled_neighbor_conjugate_base q p s c B5 hi e f hleft hz hfive Eu hEu hBu
  let ag:=sourceGraphEquiv p B5 c e hz g hg
  have hcg:ag Eu=x:=hgEu
  have hcardEu:Nat.card (Γ.neighborSet Eu)=2 := by
    have hh:=Nat.card_congr (ag.mapNeighborSet Eu)
    rw [hcg] at hh
    exact hh.trans hcard0
  have hEuOrb:∃n:G,n∈N ∧ (p.F₁ B5).conjBy n=(Eu:Subgroup G) := by
    refine ⟨g⁻¹,N.inv_mem hg,?_⟩
    have hh:=congrArg (fun E:X=>(E:Subgroup G).conjBy g⁻¹) hgEu
    rw [sourceGraphEquiv_apply,conjBy_inv,baseVertex_coe] at hh
    exact hh.symm
  obtain ⟨_,t,_,htI,_,_,htu,htz,_,htB⟩ := source_two_transvections q c B5 e f hleft hz hfive
  obtain ⟨Et,hEtEq,hEt,hnext,hEtne,hEuFix,hall,hEuEt⟩ :=
    inverse_reflection_neighbor p s B5 hi c e hz hfive q f hleft t htu htz htB
      Eu Ezu hEu hEzu hBu hBzu hxy
  have ht:t∈N:=sourceI_normalizer_le_pairSpan_normalizer p B5 c e hz htI
  let b:=sourceGraphEquiv p B5 c e hz t⁻¹ (N.inv_mem ht)
  have hbx:b x=Et := by
    apply Subtype.ext
    rw [sourceGraphEquiv_apply]
    exact hEtEq.symm
  have hby:b Eu=Eu := by
    apply Subtype.ext
    rw [sourceGraphEquiv_apply]
    exact hEuFix
  obtain ⟨r,_,hrI,hrz,hru,hrfix⟩ := source_parabolic_reflection q p s c B5 hi e f hleft hz hfive
  have hr:r∈N:=sourceI_normalizer_le_pairSpan_normalizer p B5 c e hz hrI
  let a:=sourceGraphEquiv p B5 c e hz r hr
  have hax:a x=x := by
    apply Subtype.ext
    rw [sourceGraphEquiv_apply]
    exact hrfix _ ⟨1,conjBy_one _⟩
  have hcz:(x:Subgroup G)∈colorFamily p B5 c.z (sourceU e) c.z:=first_mem_color p B5 c e hz
  obtain ⟨hzo,huo,hzu,hcomm⟩ := source_pair_marks p B5 c e hz
  have hz1:c.z≠1:=by intro hh;rw [hh,orderOf_one] at hzo;omega
  have hu1:sourceU e≠1:=by intro hh;rw [hh,orderOf_one] at huo;omega
  have hzzu:c.z≠c.z*sourceU e:=by
    intro hh
    exact hu1 (mul_left_cancel (show c.z*sourceU e=c.z*1 by simpa using hh.symm))
  have huzu:sourceU e≠c.z*sourceU e:=by
    intro hh
    exact hz1 (mul_right_cancel (show c.z*sourceU e=1*sourceU e by simpa using hh.symm))
  have colne {v w:G} (hn:v≠w) {E F:X}
      (hE:(E:Subgroup G)∈colorFamily p B5 c.z (sourceU e) v)
      (hF:(F:Subgroup G)∈colorFamily p B5 c.z (sourceU e) w) : E≠F := by
    intro hh
    exact Set.disjoint_left.mp (colorFamily_disjoint p B5 c e hz hn) hE
      ((congrArg Subtype.val hh).symm ▸ hF)
  have hau:(a Eu:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) := by
    rw [sourceGraphEquiv_apply]
    simpa only [hru] using color_conjugate_mem p B5 c.z (sourceU e) r hr hEu
  have hay:a Eu=Ezu := by
    have hh:=a.map_rel_iff.mpr hxy
    rw [hax] at hh
    rcases (hbase _).mp hh with hh|hh
    · exact False.elim (colne huzu hEu hau hh.symm)
    · exact hh
  have hrzu:r*(c.z*sourceU e)*r⁻¹=sourceU e := by
    calc
      _=(r*c.z*r⁻¹)*(r*sourceU e*r⁻¹):=by group
      _=c.z*(c.z*sourceU e):=by rw [hrz,hru]
      _=sourceU e:=by rw [←mul_assoc,←pow_two,(orderOf_eq_prime_iff.mp hzo).1,one_mul]
  have haw:a Ezu=Eu := by
    have hm:(a Ezu:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (sourceU e) := by
      rw [sourceGraphEquiv_apply]
      simpa only [hrzu] using color_conjugate_mem p B5 c.z (sourceU e) r hr hEzu
    have hh:=a.map_rel_iff.mpr hxw
    rw [hax] at hh
    rcases (hbase _).mp hh with hh|hh
    · exact hh
    · exact False.elim (colne huzu hm hEzu hh)
  have haEt:(a Et:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (sourceU e) := by
    rw [sourceGraphEquiv_apply]
    simpa only [hrzu] using color_conjugate_mem p B5 c.z (sourceU e) r hr hEt
  have hEtEu:Et≠Eu:=(colne huzu hEu hEt).symm
  have hxEt:x≠Et:=colne hzzu hcz hEt
  have hbEt:b Et=x := by
    have hh:=b.map_rel_iff.mpr hEuEt
    rw [hby] at hh
    rcases (SimpleGraph.SixCycle.neighbors_pair Γ hcardEu hxy.symm hEuEt hxEt _).mp hh with hh|hh
    · exact hh
    · exact False.elim (hxEt (b.injective (hbx.trans hh.symm)))
  have htiZu:t⁻¹*(c.z*sourceU e)*(t⁻¹)⁻¹=c.z := by
    have hh: t*c.z*t⁻¹=c.z*sourceU e := by rw [htz,hcomm.eq]
    rw [←hh]
    group
  have hbw:(b Ezu:Subgroup G)∈colorFamily p B5 c.z (sourceU e) c.z := by
    rw [sourceGraphEquiv_apply]
    simpa only [htiZu] using color_conjugate_mem p B5 c.z (sourceU e) t⁻¹ (N.inv_mem ht) hEzu
  have hbaw:b (a Et)=a Et := by
    apply Subtype.ext
    rw [sourceGraphEquiv_apply]
    exact hall _ haEt
  have hxbw:x≠b Ezu := by
    intro hh
    exact hEtne (b.injective (hbEt.trans hh))
  have hyaw:Eu≠a Et := by
    intro hh
    exact hEtne (a.injective (hh.symm.trans haw.symm))
  let v:Fin 6→X:=![x,Eu,Et,b Ezu,a Et,Ezu]
  have hcolors:∀i,(v i:Subgroup G)∈colorFamily p B5 c.z (sourceU e) (colorWord c.z (sourceU e) i) := by
    intro i
    fin_cases i
    · exact hcz
    · exact hEu
    · exact hEt
    · exact hbw
    · exact haEt
    · exact hEzu
  have h01:=colne hzu hcz hEu
  have h02:=hxEt
  have h03:=hxbw
  have h04:=colne hzu hcz haEt
  have h05:=colne hzzu hcz hEzu
  have h12:=hEtEu.symm
  have h13:Eu≠b Ezu:=(colne hzu hbw hEu).symm
  have h14:=hyaw
  have h15:=hune
  have h23:Et≠b Ezu:=(colne hzzu hbw hEt).symm
  have h24:Et≠a Et:=(colne huzu haEt hEt).symm
  have h25:=hEtne
  have h34:=colne hzu hbw haEt
  have h35:=colne hzzu hbw hEzu
  have h45:=colne huzu haEt hEzu
  have hinj:Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (h01 hij)
    · exact False.elim (h02 hij)
    · exact False.elim (h03 hij)
    · exact False.elim (h04 hij)
    · exact False.elim (h05 hij)
    · exact False.elim (h01 hij.symm)
    · rfl
    · exact False.elim (h12 hij)
    · exact False.elim (h13 hij)
    · exact False.elim (h14 hij)
    · exact False.elim (h15 hij)
    · exact False.elim (h02 hij.symm)
    · exact False.elim (h12 hij.symm)
    · rfl
    · exact False.elim (h23 hij)
    · exact False.elim (h24 hij)
    · exact False.elim (h25 hij)
    · exact False.elim (h03 hij.symm)
    · exact False.elim (h13 hij.symm)
    · exact False.elim (h23 hij.symm)
    · rfl
    · exact False.elim (h34 hij)
    · exact False.elim (h35 hij)
    · exact False.elim (h04 hij.symm)
    · exact False.elim (h14 hij.symm)
    · exact False.elim (h24 hij.symm)
    · exact False.elim (h34 hij.symm)
    · rfl
    · exact False.elim (h45 hij)
    · exact False.elim (h05 hij.symm)
    · exact False.elim (h15 hij.symm)
    · exact False.elim (h25 hij.symm)
    · exact False.elim (h35 hij.symm)
    · exact False.elim (h45 hij.symm)
    · rfl
  have hedges:∀i,Γ.Adj (v i) (v (i+1)) := by
    intro i
    fin_cases i
    · exact hxy
    · exact hEuEt
    · have hh:=b.map_rel_iff.mpr hxw
      rwa [hbx] at hh
    · have hh:=b.map_rel_iff.mpr (a.map_rel_iff.mpr hEuEt)
      rwa [hay,hbaw] at hh
    · have hh:=a.map_rel_iff.mpr hEuEt
      rw [hay] at hh
      exact hh.symm
    · exact hxw.symm
  have orbit_closed (n:G) (hn:n∈N) (E:X)
      (hE:∃m:G,m∈N ∧ (p.F₁ B5).conjBy m=(E:Subgroup G)) :
      ∃m:G,m∈N ∧ (p.F₁ B5).conjBy m=(sourceGraphEquiv p B5 c e hz n hn E:Subgroup G) := by
    obtain ⟨m,hm,hme⟩:=hE
    refine ⟨n*m,N.mul_mem hn hm,?_⟩
    rw [conjBy_mul,hme,sourceGraphEquiv_apply]
  have hxorb:∃n:G,n∈N ∧ (p.F₁ B5).conjBy n=(x:Subgroup G):=⟨1,N.one_mem,conjBy_one _⟩
  have hEtOrb:∃n:G,n∈N ∧ (p.F₁ B5).conjBy n=(Et:Subgroup G) :=
    hbx ▸ orbit_closed t⁻¹ (N.inv_mem ht) x hxorb
  have hEzuOrb:∃n:G,n∈N ∧ (p.F₁ B5).conjBy n=(Ezu:Subgroup G) :=
    hay ▸ orbit_closed r hr Eu hEuOrb
  have horb:∀i,∃n:G,n∈N ∧ (p.F₁ B5).conjBy n=(v i:Subgroup G) := by
    intro i
    fin_cases i
    · exact hxorb
    · exact hEuOrb
    · exact hEtOrb
    · exact orbit_closed t⁻¹ (N.inv_mem ht) Ezu hEzuOrb
    · exact orbit_closed r hr Et hEtOrb
    · exact hEzuOrb
  exact ⟨v,hinj,rfl,hcolors,hedges,horb,hBu,hBzu,hnext⟩
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.SixCycle
