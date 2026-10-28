module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerPropagation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiTorusEightPath
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex

/-!
# The selected torus centralizer lies in the full third kernel

Retain the full-edge complement and its original linear part D. Its
centralizer J in Q_m is normalized by that complement. Along either
four-edge half of the selected centered eight-path, an escaping image
of J would force D into the next full local permutation kernel, by the
linear root orbit or Suzuki Sylow-center rigidity. The proved torus
kernel exclusions therefore place J successively in the three incoming
cores, so J fixes the whole eight-path. Its exact two-core lies in H,
the full third kernel, hence J lies in H and has order q.

The conclusion retains the same complement, a path fixed by its actual
centralizer, and the literal original completion maps. The earlier field,
natural-center, reciprocal-commutator and local-marking inputs remain
explicit. Irreducibility and the remaining Chapter 12/13.1 assembly are
not supplied by this centralizer calculation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed p.189, the nonbinary torus-centralizer step.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem centralizer_fixes_four_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (K : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S))).IsComplement' K)
    (hoddK : Odd (Nat.card K))
    (J D : Subgroup (G₀ L S))
    (hJ : J ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hnJ : K.map (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ normalizer (J : Set (G₀ L S)))
    (hDK : D ≤ K.map (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype)
    (hoddD : Odd (Nat.card D)) (hDJ : D ≤ centralizer (J : Set (G₀ L S)))
    (p : BasedWalk (graph (reducedFamily L S)) 4 (base (reducedFamily L S) i))
    (hp : p.Nonbacktracking)
    (hKp : K.map (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i)).subtype ≤ pathStabilizer (reducedFamily L S) p)
    (havoid : ¬ D ≤ ballKernel (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1)
    (havoid₂ : ¬ D ≤ ballKernel (reducedFamily L S) (p.2.1 : Vertex (reducedFamily L S)) 1)
    (havoid₃ : ¬ D ≤ ballKernel (reducedFamily L S) (p.2.2.1 : Vertex (reducedFamily L S)) 1) :
    J ≤ pathStabilizer (reducedFamily L S) p := by
  let F := reducedFamily L S
  let m := base F i
  let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
  let C := K.map B.subtype
  have hCodd : Odd (Nat.card C) := by rw [card_map_of_injective B.subtype_injective]; exact hoddK
  have hy : (graph F).Adj (base F (!i)) m :=
    ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
  rcases p with ⟨⟨v₁,h₁⟩,⟨⟨v₂,h₂⟩,⟨⟨v₃,h₃⟩,⟨⟨v₄,h₄⟩,u⟩⟩⟩⟩
  have h₁' : (graph F).Adj m v₁ := h₁
  have h₂' : (graph F).Adj v₁ v₂ := h₂
  have h₃' : (graph F).Adj v₂ v₃ := h₃
  have h₄' : (graph F).Adj v₃ v₄ := h₄
  have htype₁ : v₁.type = !i := Bool.eq_not_iff.mpr h₁'.1.symm
  have htype₂ : v₂.type = i := by
    have hh := Bool.eq_not_iff.mpr h₂'.1.symm
    rwa [htype₁,Bool.not_not] at hh
  have htype₃ : v₃.type = !i := Bool.eq_not_iff.mpr (htype₂ ▸ h₃'.1.symm)
  have fix (v : Vertex F) (hv : v ∈ [m,v₁,v₂,v₃,v₄]) : C ≤ stabilizer F v :=
    fun c hc => hKp hc v hv
  have hCm := fix m (by simp)
  have hC₁ := fix v₁ (by simp)
  have hC₂ := fix v₂ (by simp)
  have hC₃ := fix v₃ (by simp)
  have comp {a b : Vertex F} (hab : (graph F).Adj a b)
      (ha : C ≤ stabilizer F a) (hb : C ≤ stabilizer F b) :=
    source_edge_complement_transfer h hy hab K hK C (le_inf ha hb) hCodd
      (card_map_of_injective B.subtype_injective)
  have hJ₁ : J ≤ Q F v₁ := by
    by_contra hesc
    exact havoid (suzuki_complement_invariant_centralizer_kernel_at h (!i) hn eSuz Ry
      (by simpa only [Bool.not_not] using hRy) htype₁ h₁'.symm J C D hJ hesc
      (le_inf hCm hC₁) (comp h₁' hCm hC₁) hCodd hnJ
      (hDK.trans (le_inf hCm hC₁)) hoddD hDJ)
  have hJ₂ : J ≤ Q F v₂ := by
    by_contra hesc
    exact havoid₂ (linear_complement_invariant_centralizer_kernel_at h i e T hT
      htype₂ h₂'.symm h₃' hp.2.1 J C D hJ₁ hesc
      (le_inf hC₁ hC₂) (comp h₂' hC₁ hC₂) hCodd hnJ hDK (hDK.trans hC₃) hDJ)
  have hJ₃ : J ≤ Q F v₃ := by
    by_contra hesc
    exact havoid₃ (suzuki_complement_invariant_centralizer_kernel_at h (!i) hn eSuz Ry
      (by simpa only [Bool.not_not] using hRy) htype₃ h₃'.symm J C D hJ₂ hesc
      (le_inf hC₂ hC₃) (comp h₃' hC₂ hC₃) hCodd hnJ
      (hDK.trans (le_inf hC₂ hC₃)) hoddD hDJ)
  have hJ₄ : J ≤ stabilizer F v₄ :=
    ((hJ₃.trans (source_Z_Q_U (reduced_triple h) v₃).2).trans (ballKernel_one_le_edge F h₄')).trans inf_le_right
  intro j hj v hv
  change v ∈ [m,v₁,v₂,v₃,v₄] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact Q_le_stabilizer F _ (hJ hj)
  · exact Q_le_stabilizer F _ (hJ₁ hj)
  · exact Q_le_stabilizer F _ (hJ₂ hj)
  · exact Q_le_stabilizer F _ (hJ₃ hj)
  · exact hJ₄ hj

/-- The original selected linear torus has its full two-core centralizer in the third kernel, of order q. -/
theorem source_suzuki_selected_torus_centralizer
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
      let J := Q F m ⊓ centralizer (D : Set (G₀ L S))
      D ≠ ⊥ ∧ Odd (Nat.card D) ∧
      J ≤ H ∧ J = H ⊓ centralizer (D : Set (G₀ L S)) ∧ Nat.card J = Nat.card k ∧
      (Q F m).map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) =
        (H ⊓ centralizer (D : Set (G₀ L S))).map (G₀ L S).subtype ∧
      Nat.card ((Q F m).map (G₀ L S).subtype ⊓
        centralizer (D.map (G₀ L S).subtype : Set G) : Subgroup G) = Nat.card k ∧
      ∃ v₀ : Vertex F, ∃ p : BasedWalk (graph F) 8 v₀,
        p.Nonbacktracking ∧ (p.2.2.2.1 : Vertex F) = m ∧
        K.map B.subtype ≤ pathStabilizer F p ∧ J ≤ pathStabilizer F p := by
  let F := reducedFamily L S
  let m := base F i
  let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
  let H := ballKernel F m 3
  obtain ⟨K,hK,hoddK,hKx,hDne,hDodd,v₀,p,hp,hm,hKp,_,_,_,_,_,_,hall⟩ :=
    source_suzuki_selected_torus_eight_path h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let C := K.map B.subtype
  let D := C ⊓ star L S i
  let J := Q F m ⊓ centralizer (D : Set (G₀ L S))
  have hCm : C ≤ stabilizer F m := (map_subtype_le K).trans inf_le_right
  have hnD : C ≤ normalizer (D : Set (G₀ L S)) :=
    (le_inf C.le_normalizer (hCm.trans (star_normalized_by_vertex h i))).trans
      inf_normalizer_le_normalizer_inf
  have hnJ : C ≤ normalizer (J : Set (G₀ L S)) :=
    (le_inf (hCm.trans ((stabilizer F m).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F m)))))
      (hnD.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hDJ : D ≤ centralizer (J : Set (G₀ L S)) := le_centralizer_iff.mpr inf_le_right
  obtain ⟨hfirst,hlater⟩ := source_suzuki_odd_torus_kernel_disjoint h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
    D inf_le_right hDodd
  have avoid {N : Subgroup (G₀ L S)} (hd : Disjoint D N) : ¬ D ≤ N := by
    intro he
    exact hDne (bot_unique (fun d hmem => hd.le_bot ⟨hmem,he hmem⟩))
  have fix_four (r : BasedWalk (graph F) 4 m) (hr : r.Nonbacktracking)
      (hCr : C ≤ pathStabilizer F r) : J ≤ pathStabilizer F r := by
    let t : BasedWalk (graph F) 3 m :=
      ⟨r.1,⟨r.2.1,⟨r.2.2.1,PUnit.unit⟩⟩⟩
    have ht : t.Nonbacktracking := ⟨hr.1,hr.2.1,trivial⟩
    obtain ⟨h₂,h₃⟩ := hlater t ht
    exact centralizer_fixes_four_path h i hn e eSuz T hT Ry hRy K hK hoddK J D
      inf_le_left hnJ inf_le_left hDodd hDJ r hr hCr
      (avoid (hfirst _ r.1.property)) (avoid h₂) (avoid h₃)
  have hJp : J ≤ pathStabilizer F p := by
    rcases p with ⟨⟨v₁,h₁⟩,⟨⟨v₂,h₂⟩,⟨⟨v₃,h₃⟩,⟨⟨v₄,h₄⟩,
      ⟨⟨v₅,h₅⟩,⟨⟨v₆,h₆⟩,⟨⟨v₇,h₇⟩,⟨⟨v₈,h₈⟩,u⟩⟩⟩⟩⟩⟩⟩⟩
    change v₄ = m at hm
    subst v₄
    have h₁' : (graph F).Adj v₀ v₁ := h₁
    have h₂' : (graph F).Adj v₁ v₂ := h₂
    have h₃' : (graph F).Adj v₂ v₃ := h₃
    have h₄' : (graph F).Adj v₃ m := h₄
    have h₅' : (graph F).Adj m v₅ := h₅
    have h₆' : (graph F).Adj v₅ v₆ := h₆
    have h₇' : (graph F).Adj v₆ v₇ := h₇
    have h₈' : (graph F).Adj v₇ v₈ := h₈
    let l : BasedWalk (graph F) 4 m :=
      ⟨⟨v₃,h₄'.symm⟩,⟨⟨v₂,h₃'.symm⟩,⟨⟨v₁,h₂'.symm⟩,⟨⟨v₀,h₁'.symm⟩,PUnit.unit⟩⟩⟩⟩
    let r : BasedWalk (graph F) 4 m :=
      ⟨⟨v₅,h₅'⟩,⟨⟨v₆,h₆'⟩,⟨⟨v₇,h₇'⟩,⟨⟨v₈,h₈'⟩,PUnit.unit⟩⟩⟩⟩
    have hl : l.Nonbacktracking := ⟨hp.2.2.1.symm,hp.2.1.symm,hp.1.symm,trivial⟩
    have hr : r.Nonbacktracking := hp.2.2.2.2
    have fix (c : G₀ L S) (hc : c ∈ C) :
        ∀ v ∈ [v₀,v₁,v₂,v₃,m,v₅,v₆,v₇,v₈], c • v = v := hKp hc
    have hCl : C ≤ pathStabilizer F l := by
      intro c hc v hv
      change v ∈ [m,v₃,v₂,v₁,v₀] at hv
      have hh := fix c hc
      simp only [List.forall_mem_cons] at hh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hh.2.2.2.2.1
      · exact hh.2.2.2.1
      · exact hh.2.2.1
      · exact hh.2.1
      · exact hh.1
    have hCr : C ≤ pathStabilizer F r := by
      intro c hc v hv
      change v ∈ [m,v₅,v₆,v₇,v₈] at hv
      have hh := fix c hc
      simp only [List.forall_mem_cons] at hh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hh.2.2.2.2.1
      · exact hh.2.2.2.2.2.1
      · exact hh.2.2.2.2.2.2.1
      · exact hh.2.2.2.2.2.2.2.1
      · exact hh.2.2.2.2.2.2.2.2.1
    have hJl := fix_four l hl hCl
    have hJr := fix_four r hr hCr
    intro j hj v hv
    change v ∈ [v₀,v₁,v₂,v₃,m,v₅,v₆,v₇,v₈] at hv
    have hl' : ∀ v ∈ [m,v₃,v₂,v₁,v₀], j • v = v := hJl hj
    have hr' : ∀ v ∈ [m,v₅,v₆,v₇,v₈], j • v = v := hJr hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl' _ (by simp)
    · exact hl' _ (by simp)
    · exact hl' _ (by simp)
    · exact hl' _ (by simp)
    · exact hl' _ (by simp)
    · exact hr' _ (by simp)
    · exact hr' _ (by simp)
    · exact hr' _ (by simp)
    · exact hr' _ (by simp)
  have hJH : J ≤ H := hall J ((isPGroup_pCoreIn 2 _).to_le inf_le_left) hJp
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hHQ : H ≤ Q F m := (ballKernel_antitone F m (by omega : 2 ≤ 3)).trans
    (source_suzuki_second_kernel_le_core h (!i) eSuz (by cases i <;> exact e) hk m)
  have heq : J = H ⊓ centralizer (D : Set (G₀ L S)) :=
    le_antisymm (le_inf hJH inf_le_right) (inf_le_inf_right _ hHQ)
  have hsize : Nat.card J = Nat.card k := by
    rw [heq]
    exact (source_suzuki_odd_centralizer_layers h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
      D inf_le_right hDodd hDne).2.2.2
  have hmap : (Q F m).map (G₀ L S).subtype ⊓ centralizer (D.map (G₀ L S).subtype : Set G) =
      J.map (G₀ L S).subtype := map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective _ _
  refine ⟨K,hK,hoddK,hKx,hDne,hDodd,hJH,heq,hsize,?_,?_,v₀,p,hp,hm,hKp,hJp⟩
  · rw [hmap,heq]
  · rw [hmap,card_map_of_injective (G₀ L S).subtype_injective,hsize]
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
