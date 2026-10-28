module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootJoined

/-!
# Joined-commutator comparison at the same two selected neighbors

The original maximizing-parabolic selector retains both B-relative indices,
the whole-Z fixed equality, both generation clauses and every path overlap.
If both selected seeds remain trapped, their joined commutator has order q;
each individual commutator is either trivial or this entire subgroup. When
both are nontrivial the common subgroup lies in the full ambient-fixed Z.
This discharges the joined-actor comparison in MS93 (5.7), printed p.919.
The subsequent fixed-kernel normalization and distance exclusions remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same source selector carries the exact full joined-commutator
comparison and its ambient-fixed conclusion, at every original field degree. -/
theorem Input.replacement_equal_root_selected_joined_commutators
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a
      (geometry.Z_normal a)).relIndex (U d.radical c))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
        (U d.radical c₁) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical c) ∧
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
        (U d.radical c₂) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical c) ∧
      omegaCenter J₁ ≤ Z d.radical a ∧ omegaCenter J₂ ≤ Z d.radical a ∧
      ⁅Z d.radical c₁,Q d.radical a⁆ ≤ omegaCenter J₁ ∧
      ⁅Z d.radical c₂,Q d.radical a⁆ ≤ omegaCenter J₂ ∧
      omegaCenter J₁ ⊓ omegaCenter J₂ =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical c₁,X d.radical z ⊓ Q d.radical a⁆ ⊓
        ⁅Z d.radical c₂,X d.radical z ⊓ Q d.radical a⁆ ≤
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      (Z d.radical c₁ ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) →
        Z d.radical c₂ ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) →
        let A := X d.radical z ⊓ Q d.radical a
        let D₁ := ⁅Z d.radical c₁,A⁆
        let D₂ := ⁅Z d.radical c₂,A⁆
        let D := ⁅Z d.radical c₁ ⊔ Z d.radical c₂,A⁆
        Nat.card D=Nat.card F ∧ (D₁=⊥ ∨ D₁=D) ∧ (D₂=⊥ ∨ D₂=D) ∧
          (D₁≠⊥ → D₂≠⊥ → D ≤ Z d.radical a ⊓
            centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
        (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
    hi₁,hi₂,hcenter₁,hcenter₂,hcomm₁,hcomm₂,hcenters,hinter,
    hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,hchoice⟩ :=
      h.replacement_equal_root_moving_selected_commutators d path hb hat hfirst hct
        hmove hequal hsmall hJm
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
    hi₁,hi₂,hcenter₁,hcenter₂,hcomm₁,hcomm₂,hcenters,hinter,
    hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,?_,hchoice⟩
  intro ht₁ ht₂
  dsimp only
  let c₁ := act d.radical g⁻¹ c
  let c₂ := act d.radical x c₁
  let A := X d.radical z ⊓ Q d.radical a
  let D := ⁅Z d.radical c₁ ⊔ Z d.radical c₂,A⁆
  have hcalc : Nat.card D=Nat.card F ∧
      (⁅Z d.radical c₁,A⁆=⊥ ∨ ⁅Z d.radical c₁,A⁆=D) ∧
      (⁅Z d.radical c₂,A⁆=⊥ ∨ ⁅Z d.radical c₂,A⁆=D) := by
    obtain ⟨v,_,w,hwhich,_,_,hn,_⟩ := hchoice
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · obtain ⟨he,hcard,halt⟩ := h.replacement_equal_trapped_commutators d path hb
        ha₁ hc₁ ha₂ hc₂ (hcomm₁.trans hcenter₁) (hcomm₂.trans hcenter₂) hn ht₁ ht₂
      exact ⟨hcard,Or.inr he,halt⟩
    · obtain ⟨he,hcard,halt⟩ := h.replacement_equal_trapped_commutators d path hb
        ha₂ hc₂ ha₁ hc₁ (hcomm₂.trans hcenter₂) (hcomm₁.trans hcenter₁) hn ht₂ ht₁
      have hjoin : Z d.radical c₂ ⊔ Z d.radical c₁ = Z d.radical c₁ ⊔ Z d.radical c₂ :=
        sup_comm _ _
      change ⁅Z d.radical c₂,A⁆=⁅Z d.radical c₂ ⊔ Z d.radical c₁,A⁆ at he
      change Nat.card (⁅Z d.radical c₂ ⊔ Z d.radical c₁,A⁆ : Subgroup (FreeAmalgam d.radical))=Nat.card F at hcard
      change ⁅Z d.radical c₁,A⁆=⊥ ∨ ⁅Z d.radical c₁,A⁆=⁅Z d.radical c₂ ⊔ Z d.radical c₁,A⁆ at halt
      rw [hjoin] at he hcard halt
      exact ⟨hcard,halt,Or.inr he⟩
  refine ⟨hcalc.1,hcalc.2.1,hcalc.2.2,?_⟩
  intro hn₁ hn₂
  have he₁ := hcalc.2.1.resolve_left hn₁
  have he₂ := hcalc.2.2.resolve_left hn₂
  change ⁅Z d.radical c₁,A⁆ ⊓ ⁅Z d.radical c₂,A⁆ ≤ _ at hinter
  rwa [he₁,he₂,inf_idem] at hinter

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
