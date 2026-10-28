module
public import Theory.SpecificGroups.Suzuki.SupplementInvariantSubgroups
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNeighborOrbits
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementFixedPaths

/-!
# The complement dichotomy on the opposite source six-path

At a marked Suzuki vertex, restrict the full edge complement to the
starred endpoint and project through the original quotient marking. The
Suzuki supplement theorem shows that any invariant subgroup of the
incoming core has image of order at most q or the full Sylow image of
order q². The full image lifts to the literal orbit on the remaining
graph neighbors.

For the source path a--x--b--y--c--alpha--beta, the actual intersection
D = Q_x intersect Q_y intersect Q_alpha fixes every displayed vertex.
The common complement normalizes D. Thus either [D:D intersect Q_beta]
is at most q, or the path is right regular. Both the subgroup inclusion
and the small index retain their original completion maps.

The final theorem selects this opposite six-path and its complement
from the already constructed source-minimal nonregular path. It has no
supplied complement or fixed-path premise. The original full Borel,
minimal path and its length remain in the conclusion. Both endpoint
orientations are covered by the Boolean parameter.

This proves the right-end dichotomy in (12.8), not its small-image case's
left-end transitivity. That step still needs the source lower bound
|D| >= q⁴ and the nine-path argument; s >= 7 and the remaining full-kernel,
Suzuki-selection, binary and Chapter 12/13 assembly duties remain open.
The common Sylow and original linear/Suzuki markings are earlier inputs.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.8), printed pp.185--186, using (12.1)(c,e) and (6.7).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full edge complement gives either a small Suzuki image or the full root orbit. -/
theorem suzuki_complement_invariant_small_or_transitive
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (D C : Subgroup (G₀ L S))
    (hD : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hC : C ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S))).IsComplement'
      (C.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        stabilizer (reducedFamily L S) (base (reducedFamily L S) i))))
    (hodd : Odd (Nat.card C)) (hnorm : C ≤ normalizer (D : Set (G₀ L S))) :
    let F := reducedFamily L S
    (Q F (base F i)).relIndex D ≤ 2^(2*n+1) ∨
      ((Q F (base F i)).relIndex D = (2^(2*n+1))^2 ∧
        ∀ u v, (graph F).Adj (base F i) u → (graph F).Adj (base F i) v →
          u ≠ base F (!i) → v ≠ base F (!i) → ∃ d ∈ D, d • u = v) := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F (base F (!i)) ⊓ stabilizer F (base F i)
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hDA : D ≤ A := hD.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _))
  have hk : q.ker = (Q F (base F i)).subgroupOf A := by
    have he : q.ker = pCore 2 A := by
      ext t
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff t
    rw [he,←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hc : Nat.card (C.subgroupOf E) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv
  obtain ⟨R,hR,hcover⟩ := source_quotient_edge_complement_supplement h i hadj e
    (C.subgroupOf E) hK (hc.symm ▸ hodd)
  rw [map_subgroupOf_eq_of_le hC] at hcover
  have hPN : (D.subgroupOf A).map q ≤ normalizer (R : Set (SuzukiMatrixGroup n)) := by
    apply map_le_iff_le_comap.mpr
    rw [hR]
    intro a ha
    exact Q_le_stabilizer F _ (hD ha)
  have hp : IsPGroup 2 ((D.subgroupOf A).map q) :=
    (((isPGroup_pCoreIn 2 (stabilizer F (base F (!i)))).to_le hD).comap_subtype).map q
  have hPT : (D.subgroupOf A).map q ≤ R := by
    rw [←inf_eq_left.mpr hPN,hp.inf_normalizer_sylow R]
    exact inf_le_right
  have hnA : C.subgroupOf A ≤ normalizer (D.subgroupOf A : Set A) := by
    intro c hc
    exact le_normalizer_comap A.subtype (hnorm hc)
  have hnq : (C.subgroupOf A).map q ≤ normalizer ((D.subgroupOf A).map q : Set (SuzukiMatrixGroup n)) :=
    (map_mono hnA).trans ((D.subgroupOf A).le_normalizer_map q)
  have hi : (Q F (base F i)).relIndex D = Nat.card ((D.subgroupOf A).map q) := by
    rw [←relIndex_subgroupOf hDA,←hk,relIndex_ker]
  rcases suzuki_supplement_invariant_card_or_full hn (MulEquiv.refl _) R
    ((D.subgroupOf A).map q) ((C.subgroupOf A).map q) hPT hcover hnq with hs | hf
  · exact Or.inl (hi.trans_le hs)
  right
  have hcR : Nat.card R = (2^(2*n+1))^2 := by
    obtain ⟨f,hf,_⟩ := suzukiSylow_aligned_equiv hn (MulEquiv.refl (SuzukiMatrixGroup n)) R
    rw [←hf,card_map_of_injective f.injective,suzukiRootSubgroup_card n hn]
  refine ⟨by rw [hi,hf]; exact hcR,?_⟩
  obtain ⟨p,hp,htrans⟩ := suzuki_sylow_remaining_orbit hn R
  have hstab : (MulAction.stabilizer (SuzukiMatrixGroup n) p).comap q =
      MulAction.stabilizer A (base F (!i)) := by
    rw [←hp]
    exact hR
  intro u v hu hv hun hvn
  obtain ⟨a,ha,hau⟩ := star_locally_transitive h i hadj hu
  obtain ⟨c,hc,hcv⟩ := star_locally_transitive h i hadj hv
  obtain ⟨d,hd,he⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base q
    (D.subgroupOf A) (base F (!i)) p hstab (by rw [hf]; exact htrans)
    (⟨a,ha⟩ : A) (⟨c,hc⟩ : A)
    (by simpa only [Subgroup.mk_smul,hau] using hun)
    (by simpa only [Subgroup.mk_smul,hcv] using hvn)
  refine ⟨d,hd,?_⟩
  change (d : G₀ L S) • (a • base F (!i)) = c • base F (!i) at he
  rwa [hau,hcv] at he

/-- Apply the complement dichotomy to the source's actual opposite six-path
and its intersection of the three linear vertex cores. -/
theorem source_suzuki_opposite_six_path_small_or_right_regular
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {a x b y c : Vertex (reducedFamily L S)}
    (hax : (graph (reducedFamily L S)).Adj a x)
    (hxb : (graph (reducedFamily L S)).Adj x b)
    (hby : (graph (reducedFamily L S)).Adj b y)
    (hyc : (graph (reducedFamily L S)).Adj y c)
    (hcm : (graph (reducedFamily L S)).Adj c (base (reducedFamily L S) (!i)))
    (hba : b ≠ a) (hyx : y ≠ x) (hcb : c ≠ b)
    (hmy : base (reducedFamily L S) (!i) ≠ y) (hvc : base (reducedFamily L S) i ≠ c)
    (C : Subgroup (G₀ L S))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S))).IsComplement'
      (C.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        stabilizer (reducedFamily L S) (base (reducedFamily L S) i))))
    (hodd : Odd (Nat.card C))
    (hfix : ∀ z ∈ [a,x,b,y,c,base (reducedFamily L S) (!i),base (reducedFamily L S) i],
      C ≤ stabilizer (reducedFamily L S) z) :
    let F := reducedFamily L S
    let m := base F (!i)
    let v := base F i
    let D := (Q F x ⊓ Q F y) ⊓ Q F m
    ∃ p : SimpleGraph.BasedWalk (graph F) 6 a,
      p.vertices = [a,x,b,y,c,m,v] ∧ p.Nonbacktracking ∧
      D ≤ pathStabilizer F p ∧
      D.map (G₀ L S).subtype ≤ (pathStabilizer F p).map (G₀ L S).subtype ∧
      ((Q F v).relIndex D ≤ 2^(2*n+1) ∧
        ((Q F v).map (G₀ L S).subtype).relIndex (D.map (G₀ L S).subtype) ≤ 2^(2*n+1) ∨
        (Q F v).relIndex D = (2^(2*n+1))^2 ∧
          Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) p) := by
  let F := reducedFamily L S
  let m := base F (!i)
  let v := base F i
  let D := (Q F x ⊓ Q F y) ⊓ Q F m
  have hmv : (graph F).Adj m v :=
    ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
  let p : SimpleGraph.BasedWalk (graph F) 6 a :=
    ⟨⟨x,hax⟩,⟨⟨b,hxb⟩,⟨⟨y,hby⟩,⟨⟨c,hyc⟩,⟨⟨m,hcm⟩,⟨⟨v,hmv⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
  have hDx : D ≤ Q F x := inf_le_left.trans inf_le_left
  have hDy : D ≤ Q F y := inf_le_left.trans inf_le_right
  have hDm : D ≤ Q F m := inf_le_right
  have hDs {u z : Vertex F} (hu : D ≤ Q F u) (huz : (graph F).Adj u z) :
      D ≤ stabilizer F z :=
    ((hu.trans (source_Z_Q_U (reduced_triple h) u).2).trans
      (ballKernel_one_le_edge F huz)).trans inf_le_right
  have hDp : D ≤ pathStabilizer F p := by
    intro d hd z hz
    change z ∈ [a,x,b,y,c,m,v] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hDs hDx hax.symm hd
    · exact Q_le_stabilizer F _ (hDx hd)
    · exact hDs hDx hxb hd
    · exact Q_le_stabilizer F _ (hDy hd)
    · exact hDs hDy hyc hd
    · exact Q_le_stabilizer F m (hDm hd)
    · exact hDs hDm hmv hd
  have hnQ (z : Vertex F) : stabilizer F z ≤ normalizer (Q F z : Set (G₀ L S)) :=
    (stabilizer F z).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F z)))
  have hnorm : C ≤ normalizer (D : Set (G₀ L S)) :=
    (le_inf ((le_inf ((hfix x (by simp)).trans (hnQ x))
      ((hfix y (by simp)).trans (hnQ y))).trans inf_normalizer_le_normalizer_inf)
      ((hfix m (by simp [m,F])).trans (hnQ m))).trans inf_normalizer_le_normalizer_inf
  have hC : C ≤ stabilizer F m ⊓ stabilizer F v :=
    le_inf (hfix m (by simp [m,F])) (hfix v (by simp [v,F]))
  refine ⟨p,rfl,⟨hba,hyx,hcb,hmy,hvc,trivial⟩,hDp,map_mono hDp,?_⟩
  rcases suzuki_complement_invariant_small_or_transitive h i hn e T hT D C hDm hC hK
    hodd hnorm with hs | ⟨hi,ht⟩
  · exact Or.inl ⟨hs,(relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective).trans_le hs⟩
  · refine Or.inr ⟨hi,?_⟩
    intro u z hu hz
    obtain ⟨d,hd,he⟩ := ht u z hu.1 hz.1 hu.2 hz.2
    exact ⟨d,hDp hd,he⟩

/-- Select the opposite six-path with the same full-Borel complement as the
source-minimal nonregular path, and apply the actual three-core dichotomy. -/
theorem source_mixed_selected_opposite_six_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    ∃ l : ℕ, l+1 = sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) ∧
      ∃ j : Bool, ∃ p : SimpleGraph.BasedWalk (graph F) (l+1) (base F j),
        p.Nonbacktracking ∧ ¬ Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) p ∧
        p.toWalk.IsPath ∧ ∃ C : Subgroup (G₀ L S),
          Odd (Nat.card C) ∧ C ≤ pathStabilizer F p ∧
          C.map (G₀ L S).subtype ≤ B₀ L S ⊓ (pathStabilizer F p).map (G₀ L S).subtype ∧
          Disjoint (C.map (G₀ L S).subtype) ((commonBorel L S).pCoreIn 2) ∧
          C.map (G₀ L S).subtype ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧
          ∃ a x b y c : Vertex F, ∃ γ : SimpleGraph.BasedWalk (graph F) 6 a,
            γ.vertices = [a,x,b,y,c,base F i,base F (!i)] ∧ γ.Nonbacktracking ∧
            C ≤ pathStabilizer F γ ∧
            let D := (Q F x ⊓ Q F y) ⊓ Q F (base F i)
            D ≤ pathStabilizer F γ ∧
            D.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
            ((Q F (base F (!i))).relIndex D ≤ 2^(2*n+1) ∧
              ((Q F (base F (!i))).map (G₀ L S).subtype).relIndex
                (D.map (G₀ L S).subtype) ≤ 2^(2*n+1) ∨
              (Q F (base F (!i))).relIndex D = (2^(2*n+1))^2 ∧
                Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) γ) := by
  let F := reducedFamily L S
  obtain ⟨l,hl,j,p,hp,hpn,hps,C,hodd,hCp,hCo,hdis,hsup,htransfer,hpaths⟩ :=
    source_mixed_minimal_path_fixed_six_paths h i hn eLin eSuz T hT
  obtain ⟨γ,hfirst,hnb,hCγ,_⟩ := hpaths (!i)
  rcases γ with ⟨⟨m,hm⟩,⟨⟨c,hmc⟩,⟨⟨y,hcy⟩,⟨⟨b,hyb⟩,⟨⟨x,hbx⟩,⟨⟨a,hxa⟩,u⟩⟩⟩⟩⟩⟩
  have he : m = base F i := by simpa only [Bool.not_not] using hfirst
  subst m
  have hnbs : c ≠ base F (!i) ∧ y ≠ base F i ∧ b ≠ c ∧ x ≠ y ∧ a ≠ b :=
    ⟨hnb.1,hnb.2.1,hnb.2.2.1,hnb.2.2.2.1,hnb.2.2.2.2.1⟩
  have hfix : ∀ z ∈ [a,x,b,y,c,base F i,base F (!i)], C ≤ stabilizer F z := by
    intro z hz d hd
    apply hCγ hd z
    change z ∈ [base F (!i),base F i,c,y,b,x,a]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  have hK := htransfer (base F (!i)) (base F i) hm
    (le_inf (hfix _ (by simp)) (hfix _ (by simp)))
  obtain ⟨γ,hγv,hγn,hD,hDo,hcase⟩ := source_suzuki_opposite_six_path_small_or_right_regular
    h (!i) hn eSuz T (by simpa only [Bool.not_not] using hT)
    hxa.symm hbx.symm hyb.symm hcy.symm (by simpa only [Bool.not_not] using hmc.symm) hnbs.2.2.2.2.symm
    hnbs.2.2.2.1.symm hnbs.2.2.1.symm (by simpa only [Bool.not_not] using hnbs.2.1.symm)
    hnbs.1.symm C (by cases i <;> exact hK) hodd
    (by simpa only [Bool.not_not] using hfix)
  simp only [Bool.not_not] at hγv hD hDo hcase
  have hCγ' : C ≤ pathStabilizer F γ := by
    intro d hd z hz
    rw [hγv] at hz
    exact hfix z hz hd
  exact ⟨l,hl,j,p,hp,hpn,hps,C,hodd,hCp,hCo,hdis,hsup,a,x,b,y,c,γ,hγv,hγn,hCγ',hD,hDo,hcase⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
