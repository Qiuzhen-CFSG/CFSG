module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Basic
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover

/-!
# The literal coset geometry of a source extension

Every extended flag has a simultaneous inner representative because the whole
overlap supplements the inner group. The exact inner intersections make the
coset maps injective and reflect incidence. Thus the extension has the native
typed graph, even when its outer quotient has even order. Rooted path actions
then transfer to any completion with the same whole marked overlap.

Source: Aschbacher–Smith F.4.3–6, printed pp.274–277. This transport does not
assert the native path calculations or small-completion recognition.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁)

abbrev nativeFamily (i : Bool) : Subgroup B := if i then P₁ else P₀
abbrev family (i : Bool) : Subgroup E.carrier :=
  if i then E.right.subgroupOf E.carrier else E.left.subgroupOf E.carrier

theorem baseHom_mem_family_iff
    (hi : Function.Injective (MulAut.conj : B →* MulAut B)) (i : Bool) (b : B) :
    E.baseHom b ∈ E.family i ↔ b ∈ nativeFamily (P₀ := P₀) (P₁ := P₁) i := by
  cases i
  · exact E.conj_mem_left_iff hi b
  · exact E.conj_mem_right_iff hi b

/-- A single native element represents both cosets of any extended flag. -/
theorem exists_native_representative (a : E.carrier) :
    ∃ b : B, ∀ i, ((E.baseHom b : E.carrier) : E.carrier ⧸ E.family i) = a := by
  obtain ⟨b,d,hd,he⟩ := E.factor a a.property
  refine ⟨b, fun i => QuotientGroup.eq.mpr ?_⟩
  have hval : ((E.baseHom b)⁻¹ * a : E.carrier).val = d := by
    change (MulAut.conj b)⁻¹ * a.val = d
    rw [he, inv_mul_cancel_left]
  cases i
  · change ((E.baseHom b)⁻¹ * a : E.carrier).val ∈ E.left
    exact hval.symm ▸ hd.1
  · change ((E.baseHom b)⁻¹ * a : E.carrier).val ∈ E.right
    exact hval.symm ▸ hd.2

variable (hi : Function.Injective (MulAut.conj : B →* MulAut B))

def cosetMap (i : Bool) :
    B ⧸ nativeFamily (P₀ := P₀) (P₁ := P₁) i → E.carrier ⧸ E.family i :=
  Quotient.map E.baseHom (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact (E.baseHom_mem_family_iff hi i _).mpr (QuotientGroup.leftRel_apply.mp hab))

theorem cosetMap_injective (i : Bool) : Function.Injective (E.cosetMap hi i) := by
  intro a b hab
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective b
  apply QuotientGroup.eq.mpr
  have hh : (E.baseHom x)⁻¹ * E.baseHom y ∈ E.family i := QuotientGroup.eq.mp hab
  rw [← map_inv, ← map_mul] at hh
  exact (E.baseHom_mem_family_iff hi i _).mp hh

def vertexMap (v : Subgroup.CosetGeometry.Vertex (nativeFamily (P₀ := P₀) (P₁ := P₁))) : Subgroup.CosetGeometry.Vertex E.family :=
  ⟨v.type, E.cosetMap hi v.type v.coset⟩

@[simp] theorem vertexMap_mk (i : Bool) (b : B) :
    E.vertexMap hi (mkVertex (nativeFamily (P₀ := P₀) (P₁ := P₁)) i b) =
      mkVertex E.family i (E.baseHom b) := rfl

@[simp] theorem vertexMap_base (i : Bool) :
    E.vertexMap hi (RankTwo.base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i) = RankTwo.base E.family i := by
  change mkVertex E.family i (E.baseHom 1) = mkVertex E.family i 1
  rw [map_one]

theorem vertexMap_injective : Function.Injective (E.vertexMap hi) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hij : i = j := congrArg Subgroup.CosetGeometry.Vertex.type h
  subst j
  have hcos : E.cosetMap hi i a = E.cosetMap hi i b := by
    simpa only [vertexMap, Subgroup.CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and] using h
  exact congrArg (Subgroup.CosetGeometry.Vertex.mk i) (E.cosetMap_injective hi i hcos)

theorem vertexMap_surjective : Function.Surjective (E.vertexMap hi) := by
  rintro ⟨i,q⟩
  obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b,hb⟩ := E.exists_native_representative a
  exact ⟨mkVertex _ i b, congrArg (Subgroup.CosetGeometry.Vertex.mk i) (hb i)⟩

@[simp] theorem vertexMap_smul (a : B)
    (v : Subgroup.CosetGeometry.Vertex (nativeFamily (P₀ := P₀) (P₁ := P₁))) :
    E.vertexMap hi (a • v) = E.baseHom a • E.vertexMap hi v := by
  rcases v with ⟨i,q⟩
  obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective q
  change E.vertexMap hi (mkVertex _ i (a*b)) = E.baseHom a • E.vertexMap hi (mkVertex _ i b)
  rw [vertexMap_mk, vertexMap_mk, smul_mkVertex, map_mul]

theorem vertexMap_incident_iff (v w : Subgroup.CosetGeometry.Vertex (nativeFamily (P₀ := P₀) (P₁ := P₁))) :
    Incident E.family (E.vertexMap hi v) (E.vertexMap hi w) ↔
      Incident (nativeFamily (P₀ := P₀) (P₁ := P₁)) v w := by
  constructor
  · rintro ⟨a,hv,hw⟩
    obtain ⟨b,hb⟩ := E.exists_native_representative a
    exact ⟨b, E.cosetMap_injective hi v.type ((hb v.type).trans hv),
      E.cosetMap_injective hi w.type ((hb w.type).trans hw)⟩
  · rintro ⟨b,hv,hw⟩
    exact ⟨E.baseHom b, congrArg (E.cosetMap hi v.type) hv,
      congrArg (E.cosetMap hi w.type) hw⟩

/-- Type-preserving and base-equivariant identification with the native graph. -/
def graphIso : graph (nativeFamily (P₀ := P₀) (P₁ := P₁)) ≃g graph E.family where
  toEquiv := Equiv.ofBijective (E.vertexMap hi)
    ⟨E.vertexMap_injective hi, E.vertexMap_surjective hi⟩
  map_rel_iff' := by
    intro v w
    exact and_congr Iff.rfl (E.vertexMap_incident_iff hi v w)

/-- A native rooted path actor is still an actor in the full extension. -/
theorem rootPathTransitive_of_native
    (hi : Function.Injective (MulAut.conj : B →* MulAut B)) (i : Bool) (n : ℕ)
    (ht : RootPathTransitive (graph (nativeFamily (P₀ := P₀) (P₁ := P₁))) B
      (RankTwo.base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i) n) :
    RootPathTransitive (graph E.family) E.carrier (RankTwo.base E.family i) n := by
  let e := E.graphIso hi
  have hbase : e.symm (RankTwo.base E.family i) = RankTwo.base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i := by
    apply e.injective
    exact (e.apply_symm_apply _).trans (E.vertexMap_base hi i).symm
  intro p q hp hq
  let p' := BasedWalk.rebase hbase (p.map e.symm.toHom)
  let q' := BasedWalk.rebase hbase (q.map e.symm.toHom)
  have hp' : p'.Nonbacktracking :=
    (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((BasedWalk.nonbacktracking_map_iff e.symm.toHom
        (fun x => (e.symm.mapNeighborSet x).injective) p).mpr hp)
  have hq' : q'.Nonbacktracking :=
    (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((BasedWalk.nonbacktracking_map_iff e.symm.toHom
        (fun x => (e.symm.mapNeighborSet x).injective) q).mpr hq)
  obtain ⟨a,ha,hab⟩ := ht p' q' hp' hq'
  refine ⟨E.baseHom a, ?_, ?_⟩
  · rw [← E.vertexMap_base hi i, ← E.vertexMap_smul hi, ha]
  · have hpv : p'.vertices = p.vertices.map e.symm :=
      (BasedWalk.vertices_rebase _ _).trans (BasedWalk.vertices_map _ p)
    have hqv : q'.vertices = q.vertices.map e.symm :=
      (BasedWalk.vertices_rebase _ _).trans (BasedWalk.vertices_map _ q)
    have hh := congrArg (List.map e) hab
    rw [hpv,hqv] at hh
    simp only [List.map_map, Function.comp_def, e.apply_symm_apply] at hh
    have heq (v : Subgroup.CosetGeometry.Vertex E.family) : e (a • e.symm v) = E.baseHom a • v :=
      (E.vertexMap_smul hi a _).trans (congrArg (E.baseHom a • ·) (e.apply_symm_apply v))
    have hh' := (List.map_congr_left (fun v _ => heq v)).symm.trans hh
    simpa using hh'

theorem completion_family (hgen : P₀ ⊔ P₁ = ⊤) :
    (E.completion hgen).cosetFamily = E.family := by
  funext i
  cases i
  · exact inclusion_range E.left_le
  · exact inclusion_range E.right_le

/-- Transfer from the native graph through the full extension and its actual
universal overlap cover. No oddness of the extension degree is required. -/
theorem completion_rootPathTransitive_of_native
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (hgen : P₀ ⊔ P₁ = ⊤) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (i : Bool) (n : ℕ)
    (ht : RootPathTransitive (graph (nativeFamily (P₀ := P₀) (P₁ := P₁))) B
      (RankTwo.base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i) n) :
    RootPathTransitive (graph c.cosetFamily) M (RankTwo.base c.cosetFamily i) n := by
  apply RankTwoAmalgam.Universal.rootPathTransitive_transfer_of_overlap E.amalgam
    (E.completion hgen) c (E.completion_overlap hgen) hoverlap i n
  rw [E.completion_family hgen]
  exact E.rootPathTransitive_of_native hi i n ht

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
