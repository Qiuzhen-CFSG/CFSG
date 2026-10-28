module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEightPathCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFourthKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTorusKernelEscape
/-!
# The selected full-edge complement on a centered eight-path

Keep the original full-edge complement fixing x--m--y. Extend both
orientations by three edges with that same complement, then reverse the
left half. This constructs a nonbacktracking eight-path centered at m.
Its exact two-core is the intersection with G_m^(3), of order q; every
two-subgroup of the path fixer lies in G_m^(3). The full fourth kernel
vanishes. All statements use the original completion inclusion.

The nontrivial linear part D of the selected complement is retained. The
remaining torus step must prove that C_(Q_m)(D) fixes an eight-path of
this form; fixation by the odd complement alone does not imply that
centralizer placement. Irreducibility and the remaining Chapter 12/13.1
source assembly are not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed p.189, using the path extension in (6.7).
-/
public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
private theorem fixed_centered_eight_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {x : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (C : Subgroup (G₀ L S)) (ho : Odd (Nat.card C))
    (hC : C ≤ stabilizer (reducedFamily L S) x ⊓
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        stabilizer (reducedFamily L S) (base (reducedFamily L S) i))) :
    let F := reducedFamily L S
    ∃ v₀ : Vertex F, ∃ p : BasedWalk (graph F) 8 v₀,
      p.Nonbacktracking ∧ (p.2.2.2.1 : Vertex F) = base F i ∧ C ≤ pathStabilizer F p := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  have hy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨l,hlx,hln,hCl,_⟩ := source_mixed_odd_fixed_paths h i hn e eSuz Ry hRy C ho 3 hx
    (le_inf (hC.trans inf_le_left) (hC.trans (inf_le_right.trans inf_le_right)))
  obtain ⟨r,hry,hrn,hCr,_⟩ := source_mixed_odd_fixed_paths h i hn e eSuz Ry hRy C ho 3 hy
    (hC.trans inf_le_right)
  rcases l with ⟨⟨l₁,hl₁⟩,⟨⟨l₂,hl₂⟩,⟨⟨l₃,hl₃⟩,⟨⟨l₄,hl₄⟩,l₅⟩⟩⟩⟩
  rcases r with ⟨⟨r₁,hr₁⟩,⟨⟨r₂,hr₂⟩,⟨⟨r₃,hr₃⟩,⟨⟨r₄,hr₄⟩,r₅⟩⟩⟩⟩
  change l₁ = x at hlx
  change r₁ = y at hry
  have h₀ : r₁ ≠ l₁ := by rw [hlx,hry]; exact hne.symm
  change l₂ ≠ m ∧ l₃ ≠ l₁ ∧ l₄ ≠ l₂ ∧ True at hln
  change r₂ ≠ m ∧ r₃ ≠ r₁ ∧ r₄ ≠ r₂ ∧ True at hrn
  have hl₁' : (graph F).Adj m l₁ := hl₁
  have hl₂' : (graph F).Adj l₁ l₂ := hl₂
  have hl₃' : (graph F).Adj l₂ l₃ := hl₃
  have hl₄' : (graph F).Adj l₃ l₄ := hl₄
  have hr₁' : (graph F).Adj m r₁ := hr₁
  have hr₂' : (graph F).Adj r₁ r₂ := hr₂
  have hr₃' : (graph F).Adj r₂ r₃ := hr₃
  have hr₄' : (graph F).Adj r₃ r₄ := hr₄
  let p : BasedWalk (graph F) 8 l₄ :=
    ⟨⟨l₃,hl₄'.symm⟩,⟨⟨l₂,hl₃'.symm⟩,⟨⟨l₁,hl₂'.symm⟩,⟨⟨m,hl₁'.symm⟩,
    ⟨⟨r₁,hr₁'⟩,⟨⟨r₂,hr₂'⟩,⟨⟨r₃,hr₃'⟩,⟨⟨r₄,hr₄'⟩,PUnit.unit⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨l₄,p,⟨hln.2.2.1.symm,hln.2.1.symm,hln.1.symm,h₀,hrn⟩,rfl,?_⟩
  intro c hc z hz
  have hl : ∀ z ∈ [m,l₁,l₂,l₃,l₄], c • z = z := hCl hc
  have hr : ∀ z ∈ [m,r₁,r₂,r₃,r₄], c • z = z := hCr hc
  change z ∈ [l₄,l₃,l₂,l₁,m,r₁,r₂,r₃,r₄] at hz
  simp only [List.forall_mem_cons] at hl hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hl.2.2.2.2.1
  · exact hl.2.2.2.1
  · exact hl.2.2.1
  · exact hl.2.1
  · exact hl.1
  · exact hr.2.1
  · exact hr.2.2.1
  · exact hr.2.2.2.1
  · exact hr.2.2.2.2.1

/-- Select the original complement and a centered eight-path with its exact full-kernel intersection. -/
theorem source_suzuki_selected_torus_eight_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
    let H := ballKernel F m 3
    ∃ K : Subgroup B, (pCore 2 B).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map B.subtype ≤ stabilizer F x ∧
      let D := K.map B.subtype ⊓ star L S i
      D ≠ ⊥ ∧ Odd (Nat.card D) ∧
      ∃ v₀ : Vertex F, ∃ p : BasedWalk (graph F) 8 v₀,
        p.Nonbacktracking ∧ (p.2.2.2.1 : Vertex F) = m ∧
        K.map B.subtype ≤ pathStabilizer F p ∧
        (K.map B.subtype).map (G₀ L S).subtype ≤ (pathStabilizer F p).map (G₀ L S).subtype ∧
        (pathStabilizer F p).pCoreIn 2 = H ⊓ pathStabilizer F p ∧
        Nat.card ((pathStabilizer F p).pCoreIn 2) = Nat.card k ∧
        ((pathStabilizer F p).map (G₀ L S).subtype).pCoreIn 2 =
          (H ⊓ pathStabilizer F p).map (G₀ L S).subtype ∧
        ballKernel F m 4 = ⊥ ∧ (ballKernel F m 4).map (G₀ L S).subtype = ⊥ ∧
        ∀ E : Subgroup (G₀ L S), IsPGroup 2 E → E ≤ pathStabilizer F p → E ≤ H := by
  let F := reducedFamily L S
  let m := base F i
  let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
  obtain ⟨K,hK,ho,hKx,hDne,hDo,_⟩ := source_suzuki_selected_torus_kernel_disjoint
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hoC : Odd (Nat.card (K.map B.subtype)) := by
    rw [card_map_of_injective B.subtype_injective]; exact ho
  obtain ⟨v₀,p,hp,hm,hKp⟩ := fixed_centered_eight_path h i hn e eSuz Ry hRy hxadj hne
    (K.map B.subtype) hoC (le_inf hKx (map_subtype_le _))
  obtain ⟨hcore,hsize,hmap,hall⟩ := source_suzuki_eight_path_core h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch p hp hm
  obtain ⟨hfour,hfourmap⟩ := source_suzuki_linear_fourth_kernel_trivial h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch 4 le_rfl
  exact ⟨K,hK,ho,hKx,hDne,hDo,v₀,p,hp,hm,hKp,map_mono hKp,hcore,hsize,hmap,hfour,hfourmap,hall⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
