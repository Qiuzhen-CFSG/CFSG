module

public import CFSG.Quasithin.ChapterJ.Section05.SourceOrbit
public import Mathlib.GroupTheory.IndexNormal

/-!
# The genuine second-orbit seed in J.5.4

A Sylow five-subgroup of the recognized full Ree subgroup has order25,
whereas an ambient Sylow five-subgroup has order125. Its image is normal
in an ambient Sylow containing it, since the relative index is five.
Thus the original normalizer supplies an element outside F. The new
coset stabilizer contains the full order25 subgroup, so its point cannot
lie in the first orbit, whose stabilizers have order20480. Orbit–stabilizer
and the2304-point remainder give the source lower bound15600.

No maximal-overgroup classification is assumed here. That independent
native full-Ree classification is the subsequent step of J.5.4.
Source: Aschbacher–Smith J.5.4, printed pp.445–446.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open Centralizers Centralizers.Choices RuSubgroup
variable {G:Type*} [Group G] [Finite G] (d:LocalSetup G)
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

include d in
/-- The original J.3 source gives the order of every ambient Sylow five-group. -/
theorem ambient_sylow_five_card (Q:Sylow 5 G) : Nat.card Q=125 := by
  obtain ⟨c⟩:=SourceCompletion.exists_choices d
  let B5:Sylow 5 d.toTypeRuSetup.H:=Classical.choice inferInstance
  obtain ⟨S,_,hS,_⟩:=Section03.five_oddPart_sylow c B5 (Section03.order_source c)
  exact (Nat.card_congr (Q.equiv S).toEquiv).trans hS

/-- The actual recognized subgroup's Sylow five-groups have order25. -/
theorem recognized_sylow_five_card (F:Subgroup G) (e:F≃*ReeF4.Model 0)
    (P:Sylow 5 F) : Nat.card P=25 := by
  have hF:Nat.card F=35942400:=
    (Nat.card_congr e.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card
  rw [P.card_eq_multiplicity,hF]
  decide +kernel

include d in
/-- A normalizer of the original embedded Sylow five-group escapes the full Ree subgroup. -/
theorem exists_five_normalizer_escape (F:Subgroup G) (e:F≃*ReeF4.Model 0)
    (P:Sylow 5 F) :
    ∃g:G,g∈normalizer (((P:Subgroup F).map F.subtype):Set G) ∧ g∉F := by
  let R:Subgroup G:=(P:Subgroup F).map F.subtype
  have hR:Nat.card R=25:=by
    rw [card_map_of_injective F.subtype_injective]
    exact recognized_sylow_five_card F e P
  obtain ⟨Q,hRQ⟩:=(P.isPGroup'.map F.subtype).exists_le_sylow
  have hQ:=ambient_sylow_five_card d Q
  have hi:(R.subgroupOf (Q:Subgroup G)).index=5:=by
    have hh:=(R.subgroupOf (Q:Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRQ).toEquiv,hR,hQ] at hh
    omega
  let :(R.subgroupOf (Q:Subgroup G)).Normal:=normal_of_index_eq_minFac_card (by
    rw [hi,hQ];decide +kernel)
  have hn:(Q:Subgroup G)≤normalizer (R:Set G):=le_normalizer_of_normal_subgroupOf hRQ
  have hnot:¬(Q:Subgroup G)≤F:=by
    intro h
    have hh:=card_dvd_of_le h
    rw [hQ,(Nat.card_congr e.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card] at hh
    norm_num at hh
  obtain ⟨g,hgQ,hgF⟩:=SetLike.not_le_iff_exists.mp hnot
  exact ⟨g,hn hgQ,hgF⟩

include d in
/-- The second point lies in the actual remaining set and has a sufficiently large stabilizer. -/
theorem source_second_orbit_seed (F:Subgroup G) (e:F≃*ReeF4.Model 0) (P:Sylow 5 F)
    (δ:Cosets F) (hδ:Nat.card (stabilizer F δ)=20480)
    (hrem:(({basePoint F}:Set (Cosets F))∪orbit F δ)ᶜ.ncard=2304) :
    ∃g:G,g∈normalizer (((P:Subgroup F).map F.subtype):Set G) ∧ g∉F ∧
      (P:Subgroup F)≤stabilizer F (g•basePoint F) ∧
      g•basePoint F∈(({basePoint F}:Set (Cosets F))∪orbit F δ)ᶜ ∧
      15600≤Nat.card (stabilizer F (g•basePoint F)) := by
  obtain ⟨g,hg,hout⟩:=exists_five_normalizer_escape d F e P
  have hs:stabilizer G (g•basePoint F)=F.map (MulAut.conj g).toMonoidHom:=by
    rw [stabilizer_smul_eq_stabilizer_map_conj,stabilizer_quotient]
  have hin:((P:Subgroup F).map F.subtype)≤stabilizer G (g•basePoint F):=by
    rw [hs]
    have hh:=map_mono (f:=(MulAut.conj g).toMonoidHom) (map_subtype_le (P:Subgroup F))
    have he:((P:Subgroup F).map F.subtype).map (MulAut.conj g).toMonoidHom=
        (P:Subgroup F).map F.subtype:=mem_normalizer_iff_map_conj_eq.mp hg
    rw [he] at hh
    exact hh
  have hP:(P:Subgroup F)≤stabilizer F (g•basePoint F):=by
    intro x hx
    exact hin (mem_map_of_mem F.subtype hx)
  have hne:g•basePoint F≠basePoint F:=by
    intro he
    exact hout ((stabilizer_quotient F) ▸ he)
  have hn:g•basePoint F∉orbit F δ:=by
    rintro ⟨a,ha⟩
    have hcard:=Nat.card_congr (stabilizerEquivStabilizer ha.symm).toEquiv
    have hd:=card_dvd_of_le hP
    rw [recognized_sylow_five_card F e P,← hcard,hδ] at hd
    norm_num at hd
  have hr:g•basePoint F∈(({basePoint F}:Set (Cosets F))∪orbit F δ)ᶜ:=by
    rintro (h | h)
    · exact hne h
    · exact hn h
  have hinc:orbit F (g•basePoint F)⊆(({basePoint F}:Set (Cosets F))∪orbit F δ)ᶜ:=by
    rintro x ⟨a,rfl⟩ (hb | ho)
    · have ha:(a:G)•basePoint F=basePoint F:=
        (show (a:G)∈stabilizer G (basePoint F) from (stabilizer_quotient F).symm ▸ a.property)
      exact hne (smul_left_cancel a ((show a•(g•basePoint F)=basePoint F from hb).trans ha.symm))
    · apply hn
      simpa only [inv_smul_smul] using mem_orbit_of_mem_orbit a⁻¹ ho
  have hsize:Nat.card (orbit F (g•basePoint F))≤2304:=by
    have hh:=Set.ncard_le_ncard hinc
    rw [hrem] at hh
    exact hh
  have hc:=Nat.card_congr (orbitProdStabilizerEquivGroup F (g•basePoint F))
  rw [Nat.card_prod,(Nat.card_congr e.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card] at hc
  have hl:15600≤Nat.card (stabilizer F (g•basePoint F)):=by
    have hh:=Nat.mul_le_mul_right (Nat.card (stabilizer F (g•basePoint F))) hsize
    nlinarith
  exact ⟨g,hg,hout,hP,hr,hl⟩

end CFSG.Quasithin.ChapterJ.Section05
