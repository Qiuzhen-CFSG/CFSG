module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCriticalPlacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiOppositeSixPathRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSixPathRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLowerBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementNinePath

/-!
# The source lower bound from the marked Suzuki branch

The actual source-minimal path supplies its own odd full-Borel complement.
Extend that same complement to the normalized nine-path and transport the
prior center inclusion, commutator identity and nonzero branch to it.
Global critical-pair existence and the earlier distance-three conclusion
supply every required critical-pair placement.

The first six-path is regular. The opposite six-path is left- or right-regular.
These paths start in opposite vertex orbits, so the source minimum exceeds
six. The final theorem constructs the path, complement, neighborhood Sylows
and critical pairs internally; none is an extra geometric input.

The original quotient markings, common base Sylows, `b = 3`, natural-center,
center-cardinality and earlier commutator/action inputs remain explicit.
Exhaustive Suzuki selection, the binary alternatives, full kernel series
and the remaining (12.9)/(13.1) assembly are separate source obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7)--(12.8), printed pp.184--186, and (6.7) for the original complement.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- Both literal six-path constructions on a complement-fixed nine-path
force `7 ≤ sourceS`; all four critical pairs are derived internally. -/
theorem source_suzuki_sourceS_seven_le_on_fixed_nine_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1, Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S))⁆ ≤ Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)))
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranchw : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1, star L S (!i)⁆)
    (C : Subgroup (G₀ L S))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) : Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
          stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)))))
    (hoddC : Odd (Nat.card C))
    (hfixC : C ≤ pathStabilizer (reducedFamily L S) p) :
    7 ≤ sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) := by
  have hb : 2 < b (reducedFamily L S) := by omega
  have hc := source_mixed_nine_path_initial_critical h i hb3 hn e eSuz T hT Ry hRy hzy
    p hp hm hy
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let m := base F i
  let y := base F (!i)
  let x : Vertex F := p.1
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.1
  change (p.2.1 : Vertex F) = m at hm
  change (p.2.2.1 : Vertex F) = y at hy
  have hxm : (graph F).Adj x m := by
    rw [←hm]
    exact p.2.1.property
  have hyz : (graph F).Adj y z := by
    rw [←hy]
    exact p.2.2.2.1.property
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwc : (graph F).Adj w c := p.2.2.2.2.2.1.property
  have hxne : x ≠ y := by simpa only [hy] using hp.2.1.symm
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hzn : z ≠ m := by simpa only [hm] using hp.2.2.1
  obtain ⟨R,hR⟩ := source_common_sylow_neighbors h i T hT x hxm.symm
  obtain ⟨Rz,hRz⟩ := source_common_sylow_neighbors h (!i) Ry
    (by simpa only [Bool.not_not] using hRy) z hyz
  obtain ⟨hc6,hc2,hc8⟩ := source_mixed_nine_path_critical_pairs h i hb hn e eSuz
    T hT Ry hRy p hp hy hc
  have hbranchx : ⁅V F x 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    have hym : (graph F).Adj y m :=
      ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive h (!i) hyz hym
    have hgy : g • y = y := star_le_stabilizer (!i) hg
    have hmgw : (graph F).Adj m (g • w) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hzw
      change (graph F).Adj (g • z) (g • w) at hh
      rwa [hgz] at hh
    have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
    obtain ⟨u,hu,huw⟩ := linear_common_sylow_transitive h i e T hT
      hmgw hxm.symm hgwne hxne
    have huy : u • y = y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (reduced_triple h) m).2.trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right)) hu
    have hty : (u*g) • y = y := by rw [mul_smul,hgy,huy]
    have htw : (u*g) • w = x := by rw [mul_smul,huw]
    have hh := (map_eq_bot_iff_of_injective
      (⁅V F w 1 ⊓ Q F y,V F y 1⁆ : Subgroup (G₀ L S))
      (f := (MulAut.conj (u*g)).toMonoidHom) (MulAut.conj (u*g)).injective).not.mpr hbranchw
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hty,htw] at hh
  have hfix7 : ∀ v ∈ [v₀,x,m,y,z,w,c], C ≤ stabilizer F v := by
    intro v hv t ht
    apply hfixC ht v
    have hv' : v ∈ [v₀,(p.1 : Vertex F),p.2.1,p.2.2.1,p.2.2.2.1,
        p.2.2.2.2.1,p.2.2.2.2.2.1] := by
      simpa only [hm,hy] using hv
    have hv'' := List.mem_append_left
      [(p.2.2.2.2.2.2.1 : Vertex F),p.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.1] hv'
    simpa only [BasedWalk.vertices,List.cons_append,List.nil_append] using hv''
  have hCmy : C ≤ stabilizer F m ⊓ stabilizer F y :=
    le_inf (hfix7 m (by simp)) (hfix7 y (by simp))
  have hCxa : C ≤ stabilizer F x ⊓ stabilizer F v₀ :=
    le_inf (hfix7 x (by simp)) (hfix7 v₀ (by simp))
  have hmy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hKxa := source_edge_complement_transfer h hmy p.1.property.symm
    (C.subgroupOf (stabilizer F m ⊓ stabilizer F y)) hK C hCxa hoddC
    (Nat.card_congr (subgroupOfEquivOfLe hCmy).toEquiv).symm
  obtain ⟨γ₁,_,hγ₁,_,_,_,_,_,_,hreg₁⟩ := source_suzuki_six_path_regular
    h i hb hxm.symm hxne T R hT hR e hz hcard hcardy hzx hzy
    hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc
    p.1.property.symm hmin hnat hyz hzw.symm hwc hzn hc6 Rz hRz hbranchx
    C hKxa hoddC hfix7
  obtain ⟨γ₂,_,hγ₂,_,_,_,_,hreg₂⟩ := source_suzuki_opposite_six_path_endpoint_regular
    h i hb p hp hm hy T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hmin hnat hc6 hc2 hc8
    hbranchw hfull C hK hoddC hfixC
  have hmtype : m.type = i := rfl
  have hxtype : x.type = !i := Bool.eq_not_iff.mpr (hmtype ▸ hxm.1)
  have hatype : v₀.type = i :=
    (Bool.eq_not_iff.mpr (hxtype ▸ p.1.property.1)).trans (by simp)
  exact sourceS_seven_le_of_two_six_paths h i γ₁ γ₂ hatype hxtype hγ₁ hγ₂ hreg₁ hreg₂


set_option backward.isDefEq.respectTransparency false in
/-- DGS (12.8) at the actual earlier-source boundary: choose the source-minimal
path and its same full-Borel complement, then derive the lower bound. -/
theorem source_suzuki_sourceS_seven_le
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1, star L S (!i)⁆) :
    7 ≤ sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let m := base F i
  let y := base F (!i)
  obtain ⟨ℓ,_,j,δ,_,_,_,C,hoddC,_,_,_,_,v₀,p,hp,hm,hy,hfixC,_,hK⟩ :=
    source_mixed_minimal_path_fixed_nine_path h i hn e eSuz Ry hRy
  let x : Vertex F := p.1
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  change (p.2.1 : Vertex F) = m at hm
  change (p.2.2.1 : Vertex F) = y at hy
  have hxm : (graph F).Adj x m := by
    rw [←hm]
    exact p.2.1.property
  have hyz : (graph F).Adj y z := by
    rw [←hy]
    exact p.2.2.2.1.property
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hmy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a,ha,hay⟩ := star_locally_transitive h i hmy hxm.symm
  have ham : a • m = m := star_le_stabilizer i ha
  have hzx : Z F x ≤ Z F m := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hzy
    change (Z F y).map (MulAut.conj a).toMonoidHom ≤ (Z F m).map (MulAut.conj a).toMonoidHom at hh
    rwa [←Z_translate F,←Z_translate F,hay,ham] at hh
  have hcommx : ⁅V F x 1,Q F x⁆ ≤ Z F x := by
    have hh := congrArg (fun H : Subgroup (G₀ L S) => H.map (MulAut.conj a).toMonoidHom) hcommy
    change (⁅V F y 1,Q F y⁆ : Subgroup (G₀ L S)).map (MulAut.conj a).toMonoidHom =
      (Z F y).map (MulAut.conj a).toMonoidHom at hh
    rw [map_commutator,←V_translate F,←Q_translate F,←Z_translate F,hay] at hh
    exact hh.le
  have hbranchw : ⁅V F w 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive h (!i) hyz hmy.symm
    have hgy : g • y = y := star_le_stabilizer (!i) hg
    have hmgw : (graph F).Adj m (g • w) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hzw
      change (graph F).Adj (g • z) (g • w) at hh
      rwa [hgz] at hh
    have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
    obtain ⟨u,hu,huw⟩ := linear_common_sylow_transitive h i e T hT hmgw hx₀ hgwne hx₀n
    have huy : u • y = y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (reduced_triple h) m).2.trans
          (ballKernel_one_le_edge F hmy)).trans inf_le_right)) hu
    have hty : (u*g) • y = y := by rw [mul_smul,hgy,huy]
    have htw : (u*g) • w = x₀ := by rw [mul_smul,huw]
    intro he
    have hh := congrArg (fun H : Subgroup (G₀ L S) =>
      H.map (MulAut.conj (u*g)).toMonoidHom) he
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hty,htw,Subgroup.map_bot] at hh
    exact hbranch hh
  exact source_suzuki_sourceS_seven_le_on_fixed_nine_path h i hb3 p hp hm hy T hT e
    hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy
    hmin hnat hbranchw hfull C hK hoddC hfixC

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
