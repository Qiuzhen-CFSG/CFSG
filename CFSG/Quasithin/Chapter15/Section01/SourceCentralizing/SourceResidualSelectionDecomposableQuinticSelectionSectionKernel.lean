module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionMarkedFusion
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The kernel of the original order-four partner section

An element acting trivially on F/Uc normalizes E. Thompson weak closure
corrects its action on E inside C_G(E) to an element of M intersect Mc.
That element permutes the original two marked planes. A full diagonal
in an elementary abelian direct product is fixed by every such action
that is trivial modulo the diagonal. Thus the original section kernel
centralizes Uc; no generic normalizer-quotient kernel assertion is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem diagonal_kernel_fixes
    {X : Type*} [CommGroup X] [IsElementaryAbelian 2 X]
    (A B U : Subgroup X) (hAB : A⊔B=⊤)
    (hdA : Disjoint U A) (hdB : Disjoint U B)
    (α : MulAut X) (hmove : ∀x:X, α x*x⁻¹∈U)
    (hperm : ((∀a∈A, α a∈A) ∧ (∀b∈B, α b∈B)) ∨
      ((∀a∈A, α a∈B) ∧ (∀b∈B, α b∈A))) :
    ∀u∈U, α u=u := by
  have hinv (x:X) : x⁻¹=x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) x
  intro u hu
  obtain ⟨a,ha,b,hb,he⟩ := mem_sup.mp (show u∈A⊔B from hAB ▸ mem_top u)
  rcases hperm with hp|hp
  · have hfa : α a=a := mul_inv_eq_one.mp
      (disjoint_def.mp hdA (hmove a) (A.mul_mem (hp.1 a ha) (A.inv_mem ha)))
    have hfb : α b=b := mul_inv_eq_one.mp
      (disjoint_def.mp hdB (hmove b) (B.mul_mem (hp.2 b hb) (B.inv_mem hb)))
    rw [←he,map_mul,hfa,hfb]
  · have hfa : α a=b := by
      have hh : α a*b∈U := by
        have hh:=U.mul_mem (hmove a) hu
        rw [←he] at hh
        convert hh using 1
        group
      have hh' := disjoint_def.mp hdB hh (B.mul_mem (hp.1 a ha) hb)
      simpa only [hinv] using eq_inv_of_mul_eq_one_left hh'
    have hfb : α b=a := by
      have hh : α b*a∈U := by
        have hh:=U.mul_mem (hmove b) hu
        rw [←he,mul_comm a b] at hh
        simpa only [mul_assoc,inv_mul_cancel_left] using hh
      have hh' := disjoint_def.mp hdA hh (A.mul_mem (hp.2 b hb) ha)
      simpa only [hinv] using eq_inv_of_mul_eq_one_left hh'
    rw [←he,map_mul,hfa,hfb,mul_comm b a]

/-- The kernel on the actual partner section F/Uc fixes Uc pointwise. -/
theorem PreparedChosenModule.decomposable_five_partner_four_section_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let C := centralizer (Uc:Set G)
      let F := conjugateSpanBy E C
      commutatorPreimage Mc F Uc ≤ centralizer (Uc:Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc:Set G)
  let F := conjugateSpanBy E C
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let P := commutatorPreimage Mc F Uc
  let J := elementaryAbelianMaxJ (T:Subgroup G)
  let K := centralizer (E:Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨hEN,hIE,hUE⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨hd₁,hd₂,_,_,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hMcU : Mc≤normalizer (Uc:Set G) := le_normalizer_conjugateSpanBy _ _
  have hmove : ⁅P,E⁆≤Uc := (commutator_mono le_rfl (le_conjugateSpanBy E C)).trans
    (commutator_commutatorPreimage_le Mc F Uc hMcU)
  have hPE : P≤normalizer (E:Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hmove.trans hUE)
  have hJK : J≤K := (hJ.trans (centralizer_le h.le_local)).trans
    (centralizer_le (show E≤V from inf_le_left))
  have hKMc : K≤Mc := (Subgroup.centralizer_le_normalizer (E:Set G)).trans hEN
  change P≤C
  intro g hg
  have hgMc : g∈Mc := commutatorPreimage_le Mc F Uc hg
  have hgE : g∈normalizer (E:Set G) := hPE hg
  have hgJK : J.map (MulAut.conj g).toMonoidHom≤K :=
    (map_mono hJK).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer_le_normalizer_centralizer E) hgE))
  obtain ⟨k,hk⟩ := Sylow.WeakClosure.normalizer_correction T J
    (sSup_le fun _ hA=>hA.1) (maxJ_weakly_closed_normalizer T) K hJK g hgJK
  let n := (k:G)*g
  have hnM : n∈M := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hk
  have hnMc : n∈Mc := Mc.mul_mem (hKMc k.property) hgMc
  have hnE : n∈normalizer (E:Set G) := hIE ⟨hnM,hnMc⟩
  have hact (e:G) (he:e∈E) : n*e*n⁻¹=g*e*g⁻¹ := by
    have hge : g*e*g⁻¹∈E := (mem_normalizer_iff.mp hgE e).mp he
    calc
      _=(k:G)*(g*e*g⁻¹)*(k:G)⁻¹ := by dsimp [n]; group
      _=g*e*g⁻¹ := by rw [←k.property _ hge,mul_inv_cancel_right]
  have hnmove (e:G) (he:e∈E) : ⁅n,e⁆∈Uc := by
    change (n*e*n⁻¹)*e⁻¹∈Uc
    rw [hact e he]
    exact commutator_le.mp hmove g hg e he
  let α : MulAut E := E.normalizerMonoidHom ⟨n,hnE⟩
  let a : internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict ⟨n,hnM⟩
  have hnmap : E.map (MulAut.conj n).toMonoidHom=E :=
    mem_normalizer_iff_map_conj_eq.mp hnE
  have hmap (i:d.Index) :
      (thompsonPlane T V (c.ambientFactor d i).space).map (MulAut.conj n).toMonoidHom=
      thompsonPlane T V (c.ambientFactor d (π a i)).space := by
    change ((plane _ _)⊓E).map _=(plane _ _)⊓E
    rw [map_inf _ _ _ (MulAut.conj n).injective,
      hnmap,plane_conjugate h.normalized _ ⟨n,hnM⟩]
    exact congrArg (fun P=>plane V P⊓E) (hs a i)
  have hpermi : (π a s.first=s.first ∧ π a s.second=s.second) ∨
      (π a s.first=s.second ∧ π a s.second=s.first) := by
    rcases s.covers (π a s.first) with hi|hi
    · left
      refine ⟨hi,?_⟩
      rcases s.covers (π a s.second) with hj|hj
      · exact (s.distinct ((π a).injective (hi.trans hj.symm))).elim
      · exact hj
    · right
      refine ⟨hi,?_⟩
      rcases s.covers (π a s.second) with hj|hj
      · exact hj
      · exact (s.distinct ((π a).injective (hi.trans hj.symm))).elim
  have hmapmem (i j:d.Index) (hij:π a i=j) (x:E)
      (hx:x∈(thompsonPlane T V (c.ambientFactor d i).space).subgroupOf E) :
      α x∈(thompsonPlane T V (c.ambientFactor d j).space).subgroupOf E := by
    change n*(x:G)*n⁻¹∈thompsonPlane T V (c.ambientFactor d j).space
    have hh:=hmap i
    rw [hij] at hh
    exact hh ▸ mem_map_of_mem (MulAut.conj n).toMonoidHom hx
  have hAB : Z₁.subgroupOf E⊔Z₂.subgroupOf E=⊤ := by
    rw [←subgroupOf_sup (show Z₁≤E from inf_le_right) (show Z₂≤E from inf_le_right),
      ←s.thompson_split,subgroupOf_self]
  have hdis (Z:Subgroup G) (hz:Disjoint Uc Z) :
      Disjoint (Uc.subgroupOf E) (Z.subgroupOf E) := by
    apply disjoint_def.mpr
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hz hx hy)
  have hfix := diagonal_kernel_fixes (Z₁.subgroupOf E) (Z₂.subgroupOf E)
    (Uc.subgroupOf E) hAB (hdis Z₁ hd₁) (hdis Z₂ hd₂) α
    (fun e=>hnmove e e.property) (by
      rcases hpermi with hp|hp
      · exact Or.inl ⟨hmapmem s.first s.first hp.1,hmapmem s.second s.second hp.2⟩
      · exact Or.inr ⟨hmapmem s.first s.second hp.1,hmapmem s.second s.first hp.2⟩)
  intro u hu
  have he : n*u*n⁻¹=u := congrArg Subtype.val (hfix ⟨u,hUE hu⟩ hu)
  rw [hact u (hUE hu)] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.Chapter15.Section01
