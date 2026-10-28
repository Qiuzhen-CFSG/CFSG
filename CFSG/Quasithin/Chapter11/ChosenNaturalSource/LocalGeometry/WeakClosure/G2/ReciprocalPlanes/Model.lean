module
public import Theory.Representation.G2NaturalRootCentralizers
public import Theory.Representation.G2OrthogonalCover.RootGeometry

/-!
# Full displacement planes for reciprocal G₂ roots

Every nontrivial subgroup of a long root has the full natural field plane
as its binary displacement space. A single nonidentity root parameter suffices:
dividing the two free coordinates by that parameter realizes every plane vector.
The calculation is transported by the same model conjugator as the actor.
Transfer applies it to the literal reciprocal root actions of original 11.2.2(5).

Source: Aschbacher--Smith B.4.6 and 11.2.2(5), printed pp.88--90,768.
The root formulas use the existing attributed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. No new ATLAS source is copied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover Atlas.G2.Explicit
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem root_displacement (t : F) (v : Natural.Space F) :
    Natural.action F (rootA t) v - v ∈ naturalPlane F := by
  obtain ⟨x,rfl⟩ := mk_surjective F v
  refine ⟨OrthogonalCover.action F (longRootElement F t) x-x,?_,?_⟩
  · rw [longRoot_displacement]
    exact ⟨_,rfl⟩
  · rw [map_sub]
    rfl

omit [Algebra (ZMod 2) F] in
private theorem root_displacement_surjective (t : F) (ht : t ≠ 0)
    (v : Natural.Space F) (hv : v ∈ naturalPlane F) :
    ∃ x : Natural.Space F, Natural.action F (rootA t) x-x=v := by
  obtain ⟨_,⟨w,rfl⟩,rfl⟩ := hv
  let x : TraceZero F := ⟨![0,0,0,0,0,0,-(w 0/t),w 1/t],by simp [Atlas.SplitOctonion.trace]⟩
  refine ⟨mk F x,?_⟩
  have he : OrthogonalCover.action F (longRootElement F t) x-x = planeLift F w := by
    rw [longRoot_displacement]
    congr 1
    ext i
    fin_cases i <;> simp [x,mul_div_cancel₀,ht]
  have hh := congrArg (mk F) he
  rw [map_sub] at hh
  exact hh

omit [Algebra (ZMod 2) F] in
private theorem displacement_conjugate (u b : Model F) (v : Natural.Space F) :
    Natural.action F (MulAut.conj u b) v-v =
      Natural.action F u (Natural.action F b (Natural.action F u⁻¹ v)-Natural.action F u⁻¹ v) := by
  simp only [MulAut.conj_apply,map_mul,Module.End.mul_apply,map_sub,
    (Natural.action F).self_inv_apply]

/-- Any nontrivial subgroup of a long root moves the entire marked field plane,
including when its parameter subgroup is proper over the prime field. -/
theorem root_coinvariants (B : Subgroup (Model F)) (u : Model F)
    (hB : B ≤ LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom)
    (hne : B ≠ ⊥) :
    Coinvariants.ker ((restrictScalars (k:=ZMod 2) (Natural.action F)).comp B.subtype) =
      ((naturalPlane F).map (Natural.action F u)).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨b,v⟩,rfl⟩
    obtain ⟨_,⟨t,rfl⟩,hb⟩ := hB b.property
    change Natural.action F b.val v-v ∈ (naturalPlane F).map (Natural.action F u)
    rw [←hb]
    change Natural.action F (MulAut.conj u (rootA t.toAdd)) v-v ∈ _
    rw [displacement_conjugate]
    exact ⟨_,root_displacement F _ _,rfl⟩
  · obtain hbot | ⟨b,hb,hbne⟩ := B.bot_or_exists_ne_one
    · exact (hne hbot).elim
    obtain ⟨_,⟨t,rfl⟩,he⟩ := hB hb
    have ht : t.toAdd ≠ 0 := by
      intro hz
      apply hbne
      rw [←he]
      change MulAut.conj u (rootA t.toAdd) = 1
      rw [hz,rootA_zero,map_one]
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨x,hx⟩ := root_displacement_surjective F t.toAdd ht v hv
    have hh := Coinvariants.sub_mem_ker
      (ρ := (restrictScalars (k:=ZMod 2) (Natural.action F)).comp B.subtype)
      ⟨b,hb⟩ (Natural.action F u x)
    change Natural.action F b (Natural.action F u x)-Natural.action F u x ∈ _ at hh
    rw [←he] at hh
    change Natural.action F (MulAut.conj u (rootA t.toAdd)) (Natural.action F u x)-Natural.action F u x ∈ _ at hh
    rw [displacement_conjugate,(Natural.action F).inv_self_apply,hx] at hh
    exact hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
