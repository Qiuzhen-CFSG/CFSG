module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalPair
public import CFSG.Quasithin.ChapterF.Section09.CentralLabelDistance
public import Theory.GroupTheory.SubgroupConjugation

/-!
# F.9.14(3) on the original Section 13.8 critical pair

When the terminal central line enters an H-conjugate of V, transitivity
in L places its transporter in H L H. The explicit three-edge path and
the earlier lower bound give b = 3. The same factorization transports the
literal terminal Uγ back to an L-conjugate of UH. In particular the group
conjugating the span is the one obtained from the original central label.
Source: Aschbacher--Smith, F.9.14(3), p.323, used in 13.8.33.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
variable {G : Type*} [Group G] {L T H V V₁ V₃ : Subgroup G}

theorem criticalPair_label (c : CriticalPair L T H V) (z : G) (hz : z≠1)
    (hpoint : V₁=zpowers z) (hcenter : centralizer ({z}:Set G)≤H)
    (htrans : ∀v∈V,v≠1→∃l∈L,l*z*l⁻¹=v)
    (hmin : 3≤c.path.length) (h:H) (hA : c.Aone V₁ ≤ V.conjBy (h:G)) :
    c.path.length=3 ∧ ∃l∈L,
      (c.Ugamma V₃).conjBy (h:G)⁻¹=(Source.UH H V₃).conjBy l := by
  have hm : (h:G)⁻¹*((c.gb:G)*z*(c.gb:G)⁻¹)*(h:G)∈V := by
    have hzA : (c.gb:G)*z*(c.gb:G)⁻¹∈c.Aone V₁ := by
      refine ⟨z,?_,rfl⟩
      rw [hpoint]
      exact mem_zpowers z
    obtain ⟨v,hv,he⟩ := hA hzA
    change (h:G)*v*(h:G)⁻¹=(c.gb:G)*z*(c.gb:G)⁻¹ at he
    have he' : (h:G)⁻¹*((c.gb:G)*z*(c.gb:G)⁻¹)*(h:G)=v := by rw [←he]; group
    rwa [he']
  have hd := ChapterF.Section09.central_label_distance (L⊔T) H V z c.gb
    (inclusion le_sup_right h) hz hcenter
    (fun v hv hne => by
      obtain ⟨l,hl,he⟩:=htrans v hv hne
      exact ⟨l,mem_sup_left hl,he⟩) h.property hm
  have hdist : (graph L T H).dist (base L T H false) c.gamma≤3 := by
    rw [←c.gb_one]
    have hf : cosetFamily L T H = ChapterF.Section07.Geometry.family (L⊔T) H := by
      funext i
      cases i <;> rfl
    change (Subgroup.CosetGeometry.RankTwo.graph (cosetFamily L T H)).dist
      (CosetGeometry.base (cosetFamily L T H) false)
      (c.gb • CosetGeometry.base (cosetFamily L T H) true) ≤ 3
    rw [hf]
    exact hd
  refine ⟨le_antisymm (c.distance_eq ▸ hdist) hmin,?_⟩
  let F : Bool → Subgroup G := fun i => if i then H else L
  obtain ⟨l,hl,k,hk,he⟩ := Subgroup.CosetGeometry.RankTwo.central_label_factorization
    F V z (c.gb:G) (h:G) hz hcenter htrans hm
  refine ⟨l,hl,?_⟩
  have hkfix : (Source.UH H V₃).conjBy k=Source.UH H V₃ :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H hk)
  change ((Source.UH H V₃).conjBy (c.gb:G)).conjBy (h:G)⁻¹=_
  rw [he,conjBy_mul,conjBy_mul,hkfix,conjBy_inv]
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
