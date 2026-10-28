module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedRadical

/-!
# Native local exclusions for the moved J₄ residual normalizer

The literal full SL₃(4) quotient excludes the Mathieu and symmetric-linear
locals and every local with the actual L₅(2) quotient. The proved odd
centralizer of the residual excludes all conjugates of the first involution
centralizer. These exclusions apply to the full normalizer of the projected
residual, with its maximal two-local and radical geometry from MovedRadical.

NativeJankoLocalContainment lists actual subgroup embeddings and quotient
isomorphisms. Exhaustiveness of this list for the selected source normalizer
is not assumed or proved here. That remaining placement, its contradiction,
and OddKernelNormalizer assembly stay with qt-d-1222-natural-odd-kernel-normalizer.
The independent ordinary C.2.8 case stays with the fixed-summand owner.

Source: Aschbacher--Smith, proof of 4.4.3, printed p.622; GLS3 Table5.3i.
The imported native model certificates retain their ATLAS attribution.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Normalizers.FixedSummand.Centralizer

/-- Four literal local placements used in the source inspection. This definition
does not assert that they exhaust the maximal two-local subgroups of J₄. -/
def NativeJankoLocalContainment (M : Subgroup Janko4.Model) : Prop :=
  (∃ g : Janko4.Model, M ≤ (Janko4.Cardinality.max1Subgroup
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom) ∨
  (∃ g : Janko4.Model, M ≤ Janko4.InvolutionCentralizers.First.centralizer.map
    (MulAut.conj g).toMonoidHom) ∨
  (∃ g : Janko4.Model, M ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
    (MulAut.conj g).toMonoidHom) ∨
  (∃ C : Subgroup Janko4.Model, M ≤ C ∧ Nonempty ((C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2)))

private theorem odd_centralizer_not_le_conjugate_involution_centralizer
    {Q : Type*} [Group Q] [Finite Q] (X : Subgroup Q)
    (ho : Odd (Nat.card (centralizer (X : Set Q))))
    (z : Q) (hz : orderOf z = 2) (g : Q) :
    ¬ X ≤ (centralizer ({z} : Set Q)).map (MulAut.conj g).toMonoidHom := by
  intro hX
  let e := MulAut.conj g
  have hc : (centralizer ({z} : Set Q)).map e.toMonoidHom =
      centralizer ({e z} : Set Q) := by
    simpa only [Set.image_singleton] using map_centralizer_equiv ({z} : Set Q) e
  change X ≤ (centralizer ({z} : Set Q)).map e.toMonoidHom at hX
  rw [hc] at hX
  have hm : e z ∈ centralizer (X : Set Q) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hX hx)
  have horder : orderOf (e z) = 2 := (orderOf_injective e.toMonoidHom e.injective z).trans hz
  have hd : 2 ∣ Nat.card (centralizer (X : Set Q)) := by
    rw [←horder]
    exact (centralizer (X : Set Q)).orderOf_dvd_natCard hm
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)

/-- The full covering quotient and odd residual centralizer exclude each
specified native local. The odd-centralizer premise is essential here. -/
theorem janko_cover_avoids_native_locals
    (F : BinaryField) (hF : F.degree = 2) (X M : Subgroup Janko4.Model)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (ho : Odd (Nat.card (centralizer (X : Set Janko4.Model)))) (hXM : X ≤ M) :
    ¬ NativeJankoLocalContainment M := by
  rintro (⟨g,hM⟩ | ⟨g,hM⟩ | ⟨g,hM⟩ | ⟨C,hM,⟨a⟩⟩)
  · exact janko_cover_not_le_mathieu_conjugate F hF X e g (hXM.trans hM)
  · exact odd_centralizer_not_le_conjugate_involution_centralizer X ho
      Janko4.a Janko4.orderOf_a g (hXM.trans hM)
  · exact janko_cover_not_le_symmetric_linear_conjugate F hF X e g (hXM.trans hM)
  · have h := janko_cover_not_le_linear_five_local_conjugate F hF X C e a 1
    apply h
    intro x hx
    exact ⟨x,hM (hXM hx),by simp⟩

open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the four local exclusions to the full normalizer of the original
residual under its literal component projection and J₄ marking. -/
theorem moved_janko_normalizer_avoids_native_locals
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map
      (QuotientGroup.mk' (center K))).map ek.toMonoidHom
    ¬ NativeJankoLocalContainment (normalizer (X : Set Janko4.Model)) := by
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
    (QuotientGroup.mk' (center K))
  let Y := X.map ek.toMonoidHom
  obtain ⟨_,⟨a⟩⟩ := moved_projected_cover D S hA hodd K hFK
  let t := ek.subgroupMap X
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  have ho := moved_janko_residual_centralizer_odd D S hA hodd hu K hFK hf e ek
  have hc : (centralizer (X : Set (K ⧸ center K))).map ek.toMonoidHom =
      centralizer (Y : Set Janko4.Model) := by
    simpa only [Y,coe_map,MulEquiv.coe_toMonoidHom] using
      map_centralizer_equiv (X : Set (K ⧸ center K)) ek
  have hy : Odd (Nat.card (centralizer (Y : Set Janko4.Model))) := by
    rw [←hc,card_map_of_injective ek.injective]
    exact ho
  exact janko_cover_avoids_native_locals S.field hf Y _
    (q.symm.trans (a.trans e)) hy Y.le_normalizer

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
