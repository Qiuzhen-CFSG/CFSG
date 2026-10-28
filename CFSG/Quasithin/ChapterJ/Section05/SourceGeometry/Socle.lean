module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.SecondStabilizer
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Sigma
public import Theory.GroupAction.StabilizerNormalIntersection
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Thirteen
public import Theory.GroupTheory.Simple

/-!
# Excluding the socle exception on the original second suborbit

The native PSL₂(25) core maps to the actual intersection E∩F′, by simplicity
and its order7800. The proved normalizer N_F(E∩F′)=E then shows that this core
fixes only the original point in Sigma. This discharges the essential socle-
avoidance condition in the native thirteen-overgroup theorem, giving the
actual orbit alternatives without the false blanket subgroup claim.

Source: Aschbacher–Smith J.5.5(5), printed p.447, with its implicit original
point-stabilizer hypothesis retained.
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
open Tits.Max4Outer.Mixed
local instance : Fact (Nat.Prime 13):=⟨by decide⟩
variable {G:Type*} [Group G] [Finite G] (F:Subgroup G) (q:G) (hq:q∉F)
    (hs:q•(q•basePoint F)=basePoint F) {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))

include h

/-- Any native Plus marking has the original intersection with the derived full Ree group as core. -/
theorem second_pslCore_image (e:stabilizer F (g•basePoint F)≃*Plus) :
    pslCore.map ((stabilizer F (g•basePoint F)).subtype.comp e.symm.toMonoidHom)=
      stabilizer F (g•basePoint F)⊓commutator F := by
  let E:=stabilizer F (g•basePoint F)
  let j:Plus→*F:=E.subtype.comp e.symm.toMonoidHom
  let C:=pslCore.map j
  have hc:Nat.card C=7800:=by
    change Nat.card (pslCore.map j)=7800
    rw [card_map_of_injective (f:=j) (E.subtype_injective.comp e.symm.injective)]
    exact (Nat.card_congr pslCoreEquiv.toEquiv).symm.trans Tits.Max4Projective.projective_card
  have hi:Nat.card (F⧸commutator F)=2:=by
    change (commutator F).index=2
    have he:(commutator F).map h.marking.toMonoidHom=commutator (ReeF4.Model 0):=by
      rw [map_commutator_eq,MonoidHom.range_eq_top.mpr h.marking.surjective,←_root_.commutator_def]
    rw [←index_map_of_bijective (f:=h.marking.toMonoidHom) h.marking.bijective,he]
    exact Tits.ExceptionalParabolics.FullRee.derived_index
  let : IsSimpleGroup pslCore:=pslCoreEquiv.symm.isSimpleGroup
  let f:pslCore→*(F⧸commutator F):=(QuotientGroup.mk' _).comp (j.comp pslCore.subtype)
  have hf:f=1:=f.eq_one_of_isSimpleGroup_of_card_lt (by
    rw [hi,←Nat.card_congr pslCoreEquiv.toEquiv,Tits.Max4Projective.projective_card];decide)
  have hle:C≤E⊓commutator F:=by
    rintro x ⟨y,hy,rfl⟩
    refine ⟨(e.symm y).property,?_⟩
    apply (QuotientGroup.eq_one_iff _).mp
    exact DFunLike.congr_fun hf (⟨y,hy⟩:pslCore)
  exact eq_of_le_of_card_ge hle (by rw [hc,h.second_intersection_card])

/-- The actual Sigma point stabilizers avoid the core except at the original point. -/
theorem second_point_stabilizer_not_contains_core
    (e:stabilizer F (g•basePoint F)≃*Plus) {x:Cosets F}
    (hx:x∈sourceSigma F q hq hs (basePoint F)) (hne:x≠g•basePoint F) :
    ¬pslCore≤(stabilizer (stabilizer F (g•basePoint F)) x).map e.toMonoidHom := by
  intro hle
  apply hne
  apply eq_of_stabilizer_normal_intersection_le (g•basePoint F) x (commutator F)
    h.second_intersection_normalizer ((h.sigma_base F q hq hs).le hx)
  rw [←h.second_pslCore_image F q e]
  rintro a ⟨b,hb,rfl⟩
  obtain ⟨c,hc,he⟩:=hle hb
  have hh:e.symm b=c:=
    (congrArg e.symm he.symm).trans (e.symm_apply_apply c)
  change (e.symm b)•x=x
  rw [hh]
  exact hc

/-- The corrected native thirteen-overgroup alternatives on the actual second suborbit. -/
theorem sigma_orbit_card_alternatives {x:Cosets F}
    (hx:x∈sourceSigma F q hq hs (basePoint F)) (hne:x≠g•basePoint F) :
    13∣Nat.card (orbit (stabilizer F (g•basePoint F)) x) ∨
      Nat.card (orbit (stabilizer F (g•basePoint F)) x)=300 ∨
      Nat.card (orbit (stabilizer F (g•basePoint F)) x)=600 ∨
      Nat.card (orbit (stabilizer F (g•basePoint F)) x)=1200 := by
  by_cases hd:13∣Nat.card (orbit (stabilizer F (g•basePoint F)) x)
  · exact Or.inl hd
  obtain ⟨e⟩:=h.second_plus
  let K:Subgroup Plus:=(stabilizer (stabilizer F (g•basePoint F)) x).map e.toMonoidHom
  have hi:K.index=Nat.card (orbit (stabilizer F (g•basePoint F)) x):=by
    rw [index_map_of_bijective (f:=e.toMonoidHom) e.bijective]
    exact index_stabilizer _ _
  have hnot:¬13∣K.index:=by rwa [hi]
  have hmul:13∣Nat.card K*K.index:=by rw [K.card_mul_index,plus_card];decide
  have hk:13∣Nat.card K:=((by decide : Nat.Prime 13).dvd_mul.mp hmul).resolve_right hnot
  obtain ⟨L,hL⟩:=Sylow.exists_subgroup_card_pow_prime (G:=K) 13 (n:=1) (by simpa using hk)
  have hpg:IsPGroup 13 (L.map K.subtype):=(IsPGroup.of_card hL).map K.subtype
  obtain ⟨P,hP⟩:=hpg.exists_le_sylow
  have he:L.map K.subtype=(P:Subgroup Plus):=eq_of_le_of_card_ge hP (by
    rw [card_map_of_injective K.subtype_injective,hL,sylow_thirteen_card];rfl)
  have hPK:(P:Subgroup Plus)≤K:=by
    rw [←he];exact map_subtype_le L
  have hh:=thirteen_overgroup_index P K hPK
    (h.second_point_stabilizer_not_contains_core F q hq hs e hx hne)
  rw [hi] at hh
  exact Or.inr hh

end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
