module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2FixedHexagon
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2NormalizerOrder
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Recognizing the original prepared G₂ completion

The two source normalizer indices give |G| ≤ n |G₂(F)| with |F|=2^n.
If the actual coset graph has no twelve-cycle, the established girth bound
makes the endpoint map injective on its nonbacktracking six-paths. These
paths all end in the starting coset type. Their number is (q+1)q^5, whereas
that coset type has at most n(q+1)(q^4+q^2+1) vertices. Since n<q, this is
impossible. Thus the original completion has an actual twelve-cycle.

Seven-path transitivity supplies diameter six, and the checked fixed-torus
argument gives the canonical Weyl relation and actual G₂ model isomorphism.
No diameter, cycle, parabolic placement, or Weyl relation remains as a premise.
Both original parabolic maps and their whole overlap are retained, including
field four. The Chapter 12 companion supplies the strict rank-two GlobalExit.

The original preparation and compatible G₂ comparison remain inputs. Their
exhaustive construction and original uniqueness, as well as the other model
rows, remain with the generic-global assembly. This recognizes the prepared
G₂ branch and does not claim the full source 5.2.3 theorem.
Source: Aschbacher–Smith F.4.24–44, pp.287–296, and 5.3.2–4, p.659
(`refs/quasithin.pdf`). The concrete model order retains LICENSES/ATLAS.txt
attribution through the imported native model.
-/

public noncomputable section
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

private theorem six_endpoint_injective {V : Type*} {Γ : SimpleGraph V}
    (hg : ∀ v (p : Γ.Walk v v), p.IsCycle → 12 < p.length) (x : V) :
    Function.Injective (fun p : {p : BasedWalk Γ 6 x // p.Nonbacktracking} => p.val.endpoint) := by
  intro p q he
  have hp := isPath_of_nonbacktracking_of_cycle_bound hg p.val p.property (by decide : 6≤12)
  have hq := isPath_of_nonbacktracking_of_cycle_bound hg q.val q.property (by decide : 6≤12)
  have hw : p.val.toWalk = q.val.toWalk.copy rfl he.symm := by
    by_contra hne
    obtain ⟨v,_,_,c,hc,hlen⟩ := hp.exists_isCycle_length_le_add_of_ne ((Walk.isPath_copy _ rfl he.symm).mpr hq) hne
    have hh := hg v c hc
    simp only [Walk.length_copy,BasedWalk.length_toWalk] at hlen
    omega
  apply Subtype.ext
  apply BasedWalk.vertices_injective
  simpa only [Walk.support_copy,BasedWalk.support_toWalk] using congrArg Walk.support hw

private def typedEquiv {G : Type*} [Group G] (P : Bool → Subgroup G) (i : Bool) :
    {v : RankTwo.Vertex P // v.type=i} ≃ (G ⧸ P i) where
  toFun v := v.property ▸ v.val.coset
  invFun a := ⟨⟨i,a⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,a⟩,h⟩; dsimp at h; subst j; rfl
  right_inv := by intro a; rfl

namespace Completion
variable {F : Type} [Field F] [Finite F] [CharP F 2]
  {G : Type*} [Group G] [Finite G] (c : Completion F G)
local notation "q" => Nat.card F

omit [CharP F 2] [Finite G] in
private theorem six_path_card (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (x : c.Vertex) :
    Nat.card {p : BasedWalk c.graph 6 x // p.Nonbacktracking} = (q+1)*q^5 := by
  have (x : c.Vertex) : Finite (c.graph.neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [c.card_neighbors hc]; positivity)
  have hf : ∀ {x y : c.Vertex}, c.graph.Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hh := BasedWalk.card_nonbacktracking_succ c.graph (fun x : c.Vertex => x.type)
    (fun _ => q+1) hf (c.card_neighbors hc) 5 x
  simpa only [BasedWalk.forwardCount,Nat.add_sub_cancel,pow_succ,pow_zero,mul_one,one_mul,
    mul_assoc] using hh

omit [CharP F 2] in
private theorem order_factor :
    Nat.card (Model F) = Nat.card (parabolic₁ (F := F)) * ((q+1)*(q^4+q^2+1)) := by
  have hq : 1≤q := Nat.card_pos
  have hq6 : 1≤q^6 := Nat.one_le_pow 6 q hq
  have hq2 : 1≤q^2 := Nat.one_le_pow 2 q hq
  rw [card_Model,ParabolicCells.short_card,card_borel]
  zify [hq,hq6,hq2]
  ring

omit [CharP F 2] in
/-- The ambient order bound forces a twelve-cycle in the literal completion.
Otherwise the endpoints of its six-paths are all distinct in one coset type. -/
theorem exists_twelve_cycle_of_order_bound
    (hc : c.left.range ⊓ c.right.range=c.middle.range)
    {n : ℕ} (hn : n<q) (horder : Nat.card G ≤ n*Nat.card (Model F)) :
    ∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=12 := by
  classical
  by_contra hno
  have hg (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) : 12<p.length := by
    have hle := c.cycle_length_ge_twelve hc v p hp
    have hne : p.length≠12 := fun hh => hno ⟨v,p,hp,hh⟩
    omega
  let x := RankTwo.base c.cosetFamily false
  let f : {p : BasedWalk c.graph 6 x // p.Nonbacktracking} →
      {v : c.Vertex // v.type=false} := fun p =>
    ⟨p.val.endpoint, ((QuadrangleRecognition.even_length_iff (G := c.graph) (·.type) (fun h => h.1) p.val.toWalk).mp
      (by simp only [BasedWalk.length_toWalk]; decide)).symm⟩
  let : Finite {v : c.Vertex // v.type=false} := Finite.of_equiv
    (G ⧸ c.cosetFamily false) (typedEquiv c.cosetFamily false).symm
  have hi : Function.Injective f := fun p r h =>
    six_endpoint_injective hg x (congrArg Subtype.val h)
  have hcount := Nat.card_le_card_of_injective f hi
  rw [c.six_path_card hc,Nat.card_congr (typedEquiv c.cosetFamily false)] at hcount
  change (q+1)*q^5 ≤ c.left.range.index at hcount
  have hpar : Nat.card c.left.range = Nat.card (parabolic₁ (F := F)) :=
    (Nat.card_congr (MonoidHom.ofInjective c.left_injective).toEquiv).symm
  have hidx : c.left.range.index ≤ n*((q+1)*(q^4+q^2+1)) := by
    rw [order_factor] at horder
    have hh := c.left.range.card_mul_index
    rw [hpar] at hh
    rw [←hh] at horder
    have he : n*(Nat.card (parabolic₁ (F := F))*((q+1)*(q^4+q^2+1))) =
        Nat.card (parabolic₁ (F := F))*(n*((q+1)*(q^4+q^2+1))) := by ring
    rw [he] at horder
    exact Nat.le_of_mul_le_mul_left horder Nat.card_pos
  have hbound : q^5 ≤ n*(q^4+q^2+1) := by
    have hh := hcount.trans hidx
    have he : n*((q+1)*(q^4+q^2+1)) = (q+1)*(n*(q^4+q^2+1)) := by ring
    rw [he] at hh
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hq : 1<q := Finite.one_lt_card
  have hlt : n*(q^4+q^2+1) < q^5 := by
    have hnm : n≤q-1 := by omega
    have hb := Nat.mul_le_mul_right (q^4+q^2+1) hnm
    have hh : (q-1)*(q^4+q^2+1)<q^5 := by
      have hq1 : 1≤q := by omega
      zify [hq1]
      have hq' : (2:ℤ)≤q := by exact_mod_cast (show 2≤q by omega)
      have hnon : (0:ℤ)≤q-1 := by omega
      have hpos : 0 < ((q:ℤ)-1)*((q:ℤ)^3+(q:ℤ)) + 1 := by
        have hh := mul_nonneg hnon (show (0:ℤ)≤(q:ℤ)^3+(q:ℤ) by positivity)
        omega
      nlinarith
    exact hb.trans_lt hh
  omega

end Completion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open G2CompletionGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The prepared G₂ branch recognizes the actual ambient group at the original
field degree. The comparison is retained; geometric smallness is proved. -/
theorem Preparation.g2_ambient_recognition
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Nat.card F=2^n ∧ Nonempty (G ≃* Model F) := by
  obtain ⟨e,_⟩ := d.g2_thompson_counts h hH hp F he
  obtain ⟨c,_,_,_,hc,_,_,_⟩ := d.g2_ambient_completion_geometry h hH hp F e
  have hF := (d.g2_local_structure h hH.1.1.2 hp F he).1
  have hq : 2<Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  have hn : n<Nat.card F := hF.symm ▸ Nat.lt_two_pow_self
  have hex := c.exists_twelve_cycle_of_order_bound hc hn (d.g2_ambient_order_le h hH hp F he)
  exact ⟨hF,c.nonempty_mulEquiv_of_twelve_cycle hq hc hex⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
