module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CenterLayerAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow
public import Theory.Representation.SU3.BinaryDegree
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralExclusion

/-!
# The unitary alternative in the original Suzuki selection

In the contrary unitary branch of DGS (12.5), construct the actual binary
conjugation action on V_y/Z_y. A critical center escapes Q_y, so a trivial
action would make the adjacent center invariant and collapse both neighbor
spans, contradicting that critical pair. The genuine unitary degree bound
then gives |V_y/Z_y| ≥ q⁶. With the earlier |Z_y| = q, this yields |V_y| ≥ q⁷.

Both SU₃ and PSU₃ use their concrete carriers and the original endpoint
quotient map. The representation is constructed, not supplied as an extra
premise. The remote-core index bounds and subsequent centralizer propagation
remain needed to exclude the unitary alternatives. The binary unitary cases
are outside the n ≥ 2 hypothesis and retain their separate source obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.5), printed p.182, using (12.1)(e,f) and the degree bound (5.7).
-/

public noncomputable section
open Subgroup Representation BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem unitary_card_lower {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU A 3 (2^n) ∨ IsSU A 3 (2^n))
    (ρ : Representation (ZMod 2) A W) (hne : ρ ≠ 1) : (2^n)^6 ≤ Nat.card W := by
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! hh
    exact hne (MonoidHom.ext hh)
  have hd : 6*n ≤ Module.finrank (ZMod 2) W := by
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let f := e.symm.toMonoidHom.comp J.specialToProjective
      have hf : Function.Surjective f := e.symm.surjective.comp J.specialToProjective_surjective
      obtain ⟨g,hg⟩ := hnt
      obtain ⟨x,rfl⟩ := hf g
      exact Representation.SU3.BinaryDegree.finrank_ge J hn hK hconj (ρ.comp f) ⟨x,hg⟩
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      obtain ⟨g,hg⟩ := hnt
      exact Representation.SU3.BinaryDegree.finrank_ge J hn hK hconj
        (ρ.comp e.symm.toMonoidHom) ⟨e g,by
          change ρ (e.symm (e g)) ≠ 1
          simpa only [MulEquiv.symm_apply_apply] using hg⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hd)

/-- The actual unitary center quotient in the contrary branch of (12.5)
has order at least q⁶, so its full center span has order at least q⁷. -/
theorem source_unitary_selection_layer
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) (!i)) x)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n) ∨
      IsSU (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) 3 (2^n))
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = 2^n) :
    let F := reducedFamily L S
    let y := base F i
    let D := V F y 1
    let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
    let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
    (2^n)^6 ≤ Nat.card (D ⧸ (Z F y).subgroupOf D) ∧
    (2^n)^7 ≤ Nat.card D ∧
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (D ⧸ (Z F y).subgroupOf D)),
      ρ ≠ 1 ∧ ∀ u : L (if i then 1 else 0), ∀ v : D,
        (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk v))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i u : G₀ L S) * v *
            (originalActor (L := L) (S := S) i u : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (stabilizer_normalizes_V F y 1
              (star_le_stabilizer i (originalActor (L := L) (S := S) i u).property)) v).mp v.property⟩ := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let D := V F y 1
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  let : Finite D := Finite.of_injective (inclusion ((V_le_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y).trans
      (Q_le_stabilizer F y))) (inclusion_injective _)
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨ρ,hρ⟩ := exists_center_layer_action F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y A
    (star_le_stabilizer i) (star_core h i).le hcomm
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h (!i) hadj.symm hmx
  have hnt := center_layer_action_nontrivial F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb
    hc hxa hadj A (star_le_stabilizer i)
    (fun z hz => star_locally_transitive h i hadj hz) g (star_le_stabilizer (!i) hg) hgy hzy ρ hρ
  let σ := ρ.comp (originalQuotient h i).toMonoidHom
  have hσ : σ ≠ 1 := by
    intro he
    apply hnt
    apply MonoidHom.ext
    intro u
    obtain ⟨w,rfl⟩ := (originalQuotient h i).surjective u
    exact DFunLike.congr_fun he w
  have hlow : (2^n)^6 ≤ Nat.card (D ⧸ (Z F y).subgroupOf D) :=
    unitary_card_lower (W := Additive (D ⧸ (Z F y).subgroupOf D)) hn hu σ hσ
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Z F y) D bot_le (Z_le_V F y 1)
  rw [relIndex_bot_left,relIndex_bot_left,hcard] at hmul
  have hsize : (2^n)^7 ≤ Nat.card D := by
    rw [←hmul,show (2^n)^7=(2^n)*(2^n)^6 by ring]
    exact Nat.mul_le_mul_left _ hlow
  refine ⟨hlow,hsize,σ,hσ,?_⟩
  intro u v
  change (ρ ((originalQuotient h i) (QuotientGroup.mk u))
    (Additive.ofMul (QuotientGroup.mk v))).toMul = _
  rw [originalQuotient_mk]
  exact hρ (originalActor (L := L) (S := S) i u) v

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
