module
public import CFSG.Quasithin.ChapterG.Section11.NaturalEightExclusion
public import Theory.Representation.BinaryPermutation.SixDoubleNormalizer
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.AlternatingSixTensor

/-!
# Excluding the doubled natural A₆ component in the low-rank specialization

The actual whole action embeds in S₆ × S₃ with its tensor representation.
The low-rank witness has trivial S₃ coordinate, and its S₆ coordinate is
odd: an even nonidentity involution already moves four dimensions on the
double. Together with the actual A₆ component orbit it generates the full
first S₆ factor. Removing that factor from an involution leaves an
involution in the original component centralizer. That centralizer is odd
by A.1.31, so every element of the elementary actor has trivial second
coordinate. Both natural summands are consequently HX-invariant. G.10.10
puts the nonzero marked point in their zero intersection, a contradiction.

This uses the original low-rank witness and relative Sylow normality,
without asserting whole-group identification from a constituent image.
The proper marked branch is closed; solvable degree six, whole marked
G.9 hypotheses, and exchanged geometry still require source recognition.
Source: Aschbacher--Smith G.10.10, G.11.7--8, printed pp.360,366--368.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
open BinaryPermutation
private theorem multiplicity_trivial_on_involutions
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (e : H ≃* alternatingGroup (Fin 6))
    (j : G →* (Equiv.Perm (Fin 6) × Equiv.Perm (Fin 3))) (hj : Function.Injective j)
    (he : ∀ h : H, j h = ((e h).val,1))
    (ho : Odd (Nat.card (centralizer (H : Set G))))
    (a : G) (ha : (j a).2 = 1) (haodd : (j a).1.sign = -1) :
    ∀ x : G, x ^ 2 = 1 → (j x).2 = 1 := by
  have hfirst (s : Equiv.Perm (Fin 6)) : (s,1) ∈ j.range := by
    have heven (p : Equiv.Perm (Fin 6)) (hp : p.sign = 1) : (p,1) ∈ j.range := by
      obtain ⟨h,hh⟩ := e.surjective ⟨p,Equiv.Perm.mem_alternatingGroup.mpr hp⟩
      exact ⟨h,(he h).trans (by rw [hh])⟩
    rcases Int.units_eq_one_or s.sign with hs | hs
    · exact heven s hs
    · have hsign : (s * (j a).1⁻¹).sign = 1 := by rw [map_mul,map_inv,hs,haodd]; decide
      have hmem := j.range.mul_mem (heven _ hsign) (show ((j a).1,1) ∈ j.range from
        ⟨a,Prod.ext rfl ha⟩)
      simpa only [Prod.mk_mul_mk,inv_mul_cancel_right,one_mul] using hmem
  intro x hx
  obtain ⟨b,hb⟩ := hfirst (j x).1
  let c := b⁻¹ * x
  have hc : j c = (1,(j x).2) := by
    change j (b⁻¹ * x) = _
    rw [map_mul,map_inv,hb]
    exact Prod.ext (inv_mul_cancel _) (one_mul _)
  have hcH : c ∈ centralizer (H : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    apply hj
    rw [map_mul j h c,map_mul j c h,hc,he ⟨h,hh⟩]
    exact Prod.ext (by simp) (by simp)
  have hc2 : c ^ 2 = 1 := by
    apply hj
    rw [map_pow,map_one,hc]
    apply Prod.ext
    · change (1 : Equiv.Perm (Fin 6)) ^ 2 = 1
      exact one_pow 2
    · change (j x).2 ^ 2 = 1
      exact congrArg Prod.snd (show j x ^ 2 = 1 by rw [← map_pow,hx,map_one])
  let t : centralizer (H : Set G) := ⟨c,hcH⟩
  have ht2 : t ^ 2 = 1 := Subtype.ext hc2
  have ht : t = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ho.coprime_two_left
      (orderOf_dvd_of_pow_eq_one ht2) (orderOf_dvd_natCard t))
  have hc1 : c = 1 := congrArg Subtype.val ht
  have hjs := congrArg Prod.snd hc
  simpa only [hc1,map_one,Prod.snd_one] using hjs.symm

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The source low-rank witness excludes a doubled natural A₆ action on
the actual normal component orbit. No group or tensor recognition is assumed. -/
theorem not_doubled_natural_six (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥)
    (hmodel : Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
      ((alternatingNaturalRepresentation (Fin 6)).prod
        (alternatingNaturalRepresentation (Fin 6)))) : False := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have ho := natural_centralizer_odd h cover H 6 hmodel (by simp)
  obtain ⟨e,f,hf⟩ := hmodel
  obtain ⟨j,t,hj,ht,hje⟩ := SixDoubleNormalizer.exists_tensor_embedding_of_double
    ρ h.faithful H e f hf
  let τ := ThreeTensor.action (naturalRepresentation (Fin 6))
  have hrank (a : G) : finrank (ZMod 2) (RankTwo.movedSpace ρ a) =
      finrank (ZMod 2) (RankTwo.movedSpace τ (j a)) := by
    exact RankTwo.finrank_movedSpace_transport ρ (τ.comp j.range.subtype)
      (MonoidHom.ofInjective hj) t ht a
  obtain ⟨a,ha,ha2,hapos,har,hav⟩ := hw.exists_involution h.point_ne_zero
  have hja2 : j a * j a = 1 := by
    rw [← map_mul]
    have he : a * a = 1 := by simpa only [pow_two,ha2] using pow_orderOf_eq_one a
    rw [he,map_one]
  have hs : (j a).2 = 1 := by
    by_contra hne
    have hh := ThreeTensor.dimension_le_displacement (naturalRepresentation (Fin 6)) (j a) hne
    change finrank (ZMod 2) (natural (Fin 6)) ≤
      finrank (ZMod 2) (RankTwo.movedSpace τ (j a)) at hh
    rw [RankTwo.Imprimitive.AlternatingSixTensor.finrank_fourSpace,← hrank] at hh
    omega
  have hp : (j a).1 ≠ 1 := by
    intro hp
    have hh : a = 1 := hj ((Prod.ext hp hs).trans j.map_one.symm)
    simp [hh] at ha2
  have haodd : (j a).1.sign = -1 := by
    rcases Int.units_eq_one_or (j a).1.sign with he | he
    · have hr := RankTwo.Imprimitive.AlternatingSixTensor.finrank_natural_involution
        (j a).1 he (congrArg Prod.fst hja2) hp
      have hd := ThreeTensor.displacement_first (naturalRepresentation (Fin 6)) (j a).1
      rw [hr] at hd
      have heq : j a = ((j a).1,1) := Prod.ext rfl hs
      change finrank (ZMod 2) (RankTwo.movedSpace τ ((j a).1,1)) = 2 * 2 at hd
      rw [← heq,← hrank] at hd
      omega
    · exact he
  have hX (x : G) (hx : x ∈ X) : (j x).2 = 1 :=
    multiplicity_trivial_on_involutions H e j hj hje ho a hs haodd x
      (elemPow_eq_one_of_isElementaryAbelian x hx)
  let c := t.trans ThreeTensor.pairEquiv
  have hc (g : G) (hg : (j g).2 = 1) (w : V) :
      c (ρ g w) = (naturalRepresentation (Fin 6) (j g).1 (c w).1,
        naturalRepresentation (Fin 6) (j g).1 (c w).2) := by
    change ThreeTensor.pairEquiv (t (ρ g w)) = _
    rw [ht,show j g = ((j g).1,1) from Prod.ext rfl hg]
    exact ThreeTensor.pairEquiv_equivariant (naturalRepresentation (Fin 6)) (j g).1 (t w)
  let U : Submodule (ZMod 2) V :=
    LinearMap.ker ((LinearMap.snd (ZMod 2) (natural (Fin 6)) (natural (Fin 6))).comp c.toLinearMap)
  let U' : Submodule (ZMod 2) V :=
    LinearMap.ker ((LinearMap.fst (ZMod 2) (natural (Fin 6)) (natural (Fin 6))).comp c.toLinearMap)
  have hU (g : G) (hg : (j g).2 = 1) (w : V) (hw : w ∈ U) : ρ g w ∈ U := by
    change (c w).2 = 0 at hw
    change (c (ρ g w)).2 = 0
    rw [hc g hg,hw,map_zero]
  have hU' (g : G) (hg : (j g).2 = 1) (w : V) (hw : w ∈ U') : ρ g w ∈ U' := by
    change (c w).1 = 0 at hw
    change (c (ρ g w)).1 = 0
    rw [hc g hg,hw,map_zero]
  let : Nontrivial (natural (Fin 6)) := Module.nontrivial_of_finrank_pos (by
    rw [finrank_natural_even (Fin 6) (by decide)]; decide)
  obtain ⟨u,hu⟩ := exists_ne (0 : natural (Fin 6))
  have hU0 : U ≠ ⊥ := by
    intro he
    have hm : c.symm (u,0) ∈ U := by
      change (c (c.symm (u,0))).2 = 0
      rw [c.apply_symm_apply]
    rw [he] at hm
    have hh := congrArg (fun w => (c w).1) (show c.symm (u,0) = 0 from hm)
    exact hu (by simpa only [c.apply_symm_apply,map_zero,Prod.fst_zero] using hh)
  have hU'0 : U' ≠ ⊥ := by
    intro he
    have hm : c.symm (0,u) ∈ U' := by
      change (c (c.symm (0,u))).1 = 0
      rw [c.apply_symm_apply]
    rw [he] at hm
    have hh := congrArg (fun w => (c w).2) (show c.symm (0,u) = 0 from hm)
    exact hu (by simpa only [c.apply_symm_apply,map_zero,Prod.snd_zero] using hh)
  obtain ⟨S,hSv,hXS,hnS⟩ := hS
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  obtain ⟨cover⟩ := cover
  have hind := cover.component_normalizer_index_le_two hL
  have hcv : (c v).2 = 0 := h.point_mem_normal_component_subspace hn hL hm S hnX hind U
    (le_subspaceStabilizer ρ U (fun g hg => hU g (by rw [hje ⟨g,hg⟩])))
    (le_subspaceStabilizer ρ U (fun g hg => hU g (hX g hg))) hU0
  have hcv' : (c v).1 = 0 := h.point_mem_normal_component_subspace hn hL hm S hnX hind U'
    (le_subspaceStabilizer ρ U' (fun g hg => hU' g (by rw [hje ⟨g,hg⟩])))
    (le_subspaceStabilizer ρ U' (fun g hg => hU' g (hX g hg))) hU'0
  exact h.point_ne_zero (c.injective ((Prod.ext hcv' hcv).trans c.map_zero.symm))

/-- After the proper marked branch is closed, the component orbit is either
irreducible on the original module with the actual G.9 hypotheses, or the
original selected constituent has the exchanged geometry of G.10.15. -/
def WholeOrExchangedComponentReduction (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Prop :=
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      Section10.ComponentOrthogonalData ρ B L ∧
      (Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L (componentOrbit L ⊤)
        (finrank (ZMod 2) (Additive X)) ∨
        ∃ I : Submodule (ZMod 2) V,
          Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I ∧
          v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I)

/-- The low-rank specialization has no remaining proper marked constituent.
The solvable degree-six, whole-module G.9, and exchanged G.11.6 branches are
retained for their genuine source recognition. -/
theorem conclusion_or_whole_or_exchanged_component_reduction
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ WholeOrExchangedComponentReduction ρ B v W X))) := by
  rcases conclusion_or_six_natural_component_reduction h cover hw hS with
    hc | ⟨hi,hd,hs | ⟨hn,hh⟩⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · obtain ⟨L,hL,hm,horth,I,hI,hmarked | hexchanged⟩ := hh
    · obtain ⟨hv,halt,ht | ⟨hmodel,_⟩⟩ := hmarked
      · have hcH : Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L
            (componentOrbit L ⊤) (finrank (ZMod 2) (Additive X)) := by
          rcases halt.2.2.2 with ⟨_,hc⟩ | hiso
          · exact hc
          · have hz := hiso.2.1
            rw [ht,finrank_top] at hz
            omega
        exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,Or.inl hcH⟩⟩
      · exact (not_doubled_natural_six h cover hw hS hn hL hm hmodel).elim
    · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,Or.inr ⟨I,hI,hexchanged⟩⟩⟩

end CFSG.Quasithin.ChapterG.Section11
