module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootNormalization

/-!
# Backward paths in the equal-mover critical-root branch

At the original two selected neighbors, assume both seeds remain trapped.
One seed escapes endpoint normalization. Its full commutator has order q;
the second is trivial or is the same ambient-fixed subgroup. In either
case the actual three source generators normalize the same whole-Z fixed
kernel, contradicting its original B-relative moving index greater than q.

Thus one of these same neighbors yields an actual backward critical path.
The original field degree, full quotient marking, both generation identities,
whole-Z fixed equality, both B-relative indices and every overlap remain.
This closes the equal-mover root case of MS93 (5.7), printed p.919. The
contained-image choices and terminal distance exclusions remain necessary
for the minimum-characteristic-replacement distance-two witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The equal-mover critical-root selector supplies an actual backward
critical path, preserving both original B-relative indices, the full Z
fixed equality, both generation identities and every path overlap. -/
theorem Input.replacement_equal_root_backward_path
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
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  classical
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
    hi₁,hi₂,hcenter₁,hcenter₂,hcomm₁,hcomm₂,hcenters,hinter,
    hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,hcalc,hchoice⟩ :=
      h.replacement_equal_root_selected_joined_commutators d path hb hat hfirst hct
        hmove hequal hsmall hJm
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
    hi₁,hi₂,hcenter₁,hcenter₂,hcomm₁,hcomm₂,hcenters,hinter,
    hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,?_⟩
  let c₁ := act d.radical g⁻¹ c
  let c₂ := act d.radical x c₁
  let t₁ := act d.radical g⁻¹ t
  let t₂ := act d.radical x t₁
  let A := X d.radical z ⊓ Q d.radical a
  have hxS : x ∈ stabilizer d.radical a := Ltilde_le_stabilizer a hx
  have hnonzero (T : Subgroup (FreeAmalgam d.radical)) (hc : Nat.card T=Nat.card F) : T≠⊥ := by
    intro he
    rw [he] at hc
    have hc' : Nat.card F=1 := by simpa using hc.symm
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hnot : ¬ (Z d.radical c₁ ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      Z d.radical c₂ ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) := by
    rintro ⟨ht₁,ht₂⟩
    obtain ⟨hcard,halt₁,halt₂,hambient⟩ := hcalc ht₁ ht₂
    obtain ⟨v,_,w,hwhich,_,_,hn,_⟩ := hchoice
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · obtain ⟨he,hc,_⟩ := h.replacement_equal_trapped_commutators d path hb
        ha₁ hc₁ ha₂ hc₂ (hcomm₁.trans hcenter₁) (hcomm₂.trans hcenter₂) hn ht₁ ht₂
      have hn₁ : ⁅Z d.radical c₁,A⁆≠⊥ :=
        hnonzero _ ((congrArg (fun T : Subgroup (FreeAmalgam d.radical) => Nat.card T) he).trans hc)
      have he₁ := halt₁.resolve_left hn₁
      have hcommon : ⁅Z d.radical c₂,A⁆=⊥ ∨
          (⁅Z d.radical c₂,A⁆=⁅Z d.radical c₁,A⁆ ∧
            ⁅Z d.radical c₁,A⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
        by_cases hn₂ : ⁅Z d.radical c₂,A⁆=⊥
        · exact Or.inl hn₂
        · exact Or.inr ⟨(halt₂.resolve_left hn₂).trans he₁.symm,
            he₁.le.trans ((hambient hn₁ hn₂).trans inf_le_right)⟩
      exact h.replacement_equal_root_trapped_excluded d path hb ha₁ hc₁ x hxS hsmall hn hgen₁
        (by rw [hi₁]; exact hmove) hcommon ⟨ht₁,ht₂⟩
    · obtain ⟨he,hc,_⟩ := h.replacement_equal_trapped_commutators d path hb
        ha₂ hc₂ ha₁ hc₁ (hcomm₂.trans hcenter₂) (hcomm₁.trans hcenter₁) hn ht₂ ht₁
      have hn₂ : ⁅Z d.radical c₂,A⁆≠⊥ :=
        hnonzero _ ((congrArg (fun T : Subgroup (FreeAmalgam d.radical) => Nat.card T) he).trans hc)
      have he₂ := halt₂.resolve_left hn₂
      have hcommon : ⁅Z d.radical c₁,A⁆=⊥ ∨
          (⁅Z d.radical c₁,A⁆=⁅Z d.radical c₂,A⁆ ∧
            ⁅Z d.radical c₂,A⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
        by_cases hn₁ : ⁅Z d.radical c₁,A⁆=⊥
        · exact Or.inl hn₁
        · exact Or.inr ⟨(halt₁.resolve_left hn₁).trans he₂.symm,
            he₂.le.trans ((hambient hn₁ hn₂).trans inf_le_right)⟩
      have hback : act d.radical x⁻¹ c₂=c₁ := by
        dsimp only [c₂]
        rw [←act_mul,mul_inv_cancel,act_one]
      apply h.replacement_equal_root_trapped_excluded d path hb ha₂ hc₂ x⁻¹
        ((stabilizer d.radical a).inv_mem hxS) hsmall hn hgen₂ (by rw [hi₂]; exact hmove)
      · simpa only [c₂,c₁,A,←act_mul,mul_inv_cancel_right] using hcommon
      · exact ⟨ht₂,by rwa [hback]⟩
  by_cases ht₁ : Z d.radical c₁ ≤ Q d.radical (path.walk.getVert (path.walk.length-2))
  · have ht₂ : ¬ Z d.radical c₂ ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) :=
      fun ht₂ => hnot ⟨ht₁,ht₂⟩
    exact ⟨c₂,by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; exact Or.inr rfl,t₂,Or.inr ⟨rfl,rfl⟩,ha₂,hc₂,
      exists_backward_path_of_not_le geometry (by omega) path ha₂ hc₂ ht₂⟩
  · exact ⟨c₁,by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; exact Or.inl rfl,t₁,Or.inl ⟨rfl,rfl⟩,ha₁,hc₁,
      exists_backward_path_of_not_le geometry (by omega) path ha₁ hc₁ ht₁⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
