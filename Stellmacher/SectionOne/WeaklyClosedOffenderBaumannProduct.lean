module

public import Stellmacher.SectionOne.OffenderSelectedProduct
public import Stellmacher.SectionOne.OneSevenBaumann
public import Stellmacher.SectionOne.SL2FamilySylowCard
public import Theory.GroupTheory.WeakClosureFrattini

/-!
# The normal closure of a weakly closed offender subgroup

Let a finite solvable group act faithfully on an elementary abelian two-group,
with trivial two-core. An offender-generated subgroup `J` of a Sylow two-subgroup
is assumed weakly closed. If `J ≤ B ≤ S` and `B` fixes the `J`-fixed space
pointwise, then `J = B`. The full normal closure of `B` is an internal product
of the factors from (1.7), with the matching four-element commutator modules
and a common fixed complement for the original supplied action.

For nontrivial `J`, its two-group order establishes the even-order hypothesis
needed by the selected-product theorem. That theorem supplies
`E = [O_{2'}(G), J] J`, normal within the global factor product. Weak closure
and the Frattini argument upgrade this to ambient normality. Fixed-space
normalization and the faithful module order bound give `|B| ≤ |J|`, hence
`B = J`. Normality and commutator monotonicity identify `E` with the actual
normal closure. If `J` is trivial, faithfulness makes `B` trivial and the
empty factor family gives the result.

This extracts the action argument of Stellmacher (2.2), journal p.20, for use
with the original module in (4.6), p.26. Source:
`refs/latex/stellmacher-n-group.tex`; the odd-core prime follows the scan,
as recorded in `Stellmacher.SectionOne.Defs`.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u v

/-- A weakly closed offender subgroup equals every intervening subgroup fixing
its fixed space, and its normal closure has the shared factor/module product. -/
public theorem weakly_closed_offender_baumann_product
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hsol : Group.IsSolvable G)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcore : pCore 2 G = ⊥)
    (S : Sylow 2 G) {I : Sort v}
    (A : I → Subgroup G) (hA : ∀ i, oneA (V := V) (S : Subgroup G) (A i))
    (J B : Subgroup G) (hJgen : J = ⨆ i, A i)
    (hweak : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      J.map (MulAut.conj g).toMonoidHom = J)
    (hJB : J ≤ B) (hBS : B ≤ (S : Subgroup G))
    (hBfix : B ≤ fixingSubgroup G (FixedPoints.subgroup J V : Set V)) :
    let L := Subgroup.normalClosure (B : Set G)
    J = B ∧ ∃ (n : ℕ) (D : Fin n → Subgroup G),
      L = ⨆ i, D i ∧
      IsInternalDirectProductFamily L D ∧
      Function.Injective D ∧
      (∀ i, IsOneSevenFactor (V := V) (D i)) ∧
      (∀ i, ((D i).subgroupOf L).Normal) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup V)
        (fun i : Option (Fin n) => match i with
          | none => FixedPoints.subgroup L V
          | some i => commutatorAction (D i) V) := by
  classical
  by_cases hJbot : J = ⊥
  · have hfixbot : FixedPoints.subgroup (⊥ : Subgroup G) V = ⊤ := by
      ext v
      simp only [Subgroup.mem_top, iff_true, FixedPoints.mem_subgroup]
      intro g
      have hg : (g : G) = 1 := g.property
      change (g : G) • v = v
      rw [hg, one_smul]
    have hBbot : B = ⊥ := by
      apply bot_unique
      rw [hJbot, hfixbot] at hBfix
      simpa [hfaith] using hBfix
    rw [hJbot, hBbot]
    rw [Subgroup.normalClosure_eq_self]
    refine ⟨rfl, 0, (fun i : Fin 0 => Fin.elim0 i), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (iSup_of_empty _).symm
    · simp [IsInternalDirectProductFamily, iSup_of_empty]
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · refine ⟨?_, ?_, ?_⟩
      · simp only [iSup_option, iSup_of_empty, sup_bot_eq]
        exact hfixbot.symm
      · intro i j hij
        exact False.elim (hij (Subsingleton.elim i j))
      · intro i j hij
        exact False.elim (hij (Subsingleton.elim i j))
  have hJS : J ≤ (S : Subgroup G) := hJB.trans hBS
  have heven : Even (Nat.card G) := by
    have hJp := S.isPGroup'.to_le hJS
    rcases hJp.card_eq_or_dvd with hcard | hdvd
    · exact False.elim (hJbot (J.eq_bot_of_card_eq hcard))
    · exact even_iff_two_dvd.mpr (hdvd.trans J.card_subgroup_dvd_card)
  let h : Hypotheses G V := ⟨hsol, heven, hfaith, hcore⟩
  let E := ⁅oddCore G, J⁆ ⊔ J
  obtain ⟨hJinf, hEN, hEnorm, n, D, hprod, hDin, hD, hDN, hmodule⟩ :=
    offender_generated_selected_product h S A hA J hJgen
  change IsInternalDirectProductFamily E D at hprod
  let N := oneSevenGenerated (G := G) (V := V)
  let : N.Normal := (oneSeven_global_product h S).1
  have hJN : J ≤ N := (show J ≤ E from le_sup_right).trans hEN
  have hNE : N ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mp hEnorm
  have hJE : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (E : Set G) := by
    let W := oddCore G
    let : W.Normal := pPrimeCore_normal
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hW : W.map (MulAut.conj b).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (show b ∈ Subgroup.normalizer (W : Set G) by rw [Subgroup.normalizer_eq_top]; trivial)
    have hJ : J.map (MulAut.conj b).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
    change (⁅W, J⁆ ⊔ J).map (MulAut.conj b).toMonoidHom = ⁅W, J⁆ ⊔ J
    rw [Subgroup.map_sup, Subgroup.map_commutator, hW, hJ]
  have hE : E.Normal := normal_of_normalized_by_normal_and_weakly_closed_normalizer
    S N J E hJS hJN hweak hNE hJE
  have hJcard : Nat.card J = 2 ^ n := by
    rw [hJinf]
    exact sl2_family_sylow_inf_card S E hE D hDin hprod (fun i => (hD i).1) hDN
  have hJp : IsPGroup 2 J := S.isPGroup'.to_le hJS
  have hBnorm (i : Fin n) : B ≤ Subgroup.normalizer (D i : Set G) := by
    have hDE : D i ≤ E := by rw [hprod.1]; exact le_iSup D i
    have hJnorm : J ≤ Subgroup.normalizer (D i : Set G) :=
      (show J ≤ E from le_sup_right).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp (hDN i))
    exact hBfix.trans (oneSevenFactor_fixedSpace_normalizes h (D i) J (hD i) hJp hJnorm)
  have hBfixE : B ≤ fixingSubgroup G (FixedPoints.subgroup E V : Set V) := by
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply (mem_fixingSubgroup_iff (M := G)).mp (hBfix hb) v
    change v ∈ FixedPoints.subgroup J V
    rw [FixedPoints.mem_subgroup]
    intro j
    exact (FixedPoints.mem_subgroup (M := E) (a := v)).mp hv
      ⟨j, (show J ≤ E from le_sup_right) j.property⟩
  have hBp : IsPGroup 2 B := S.isPGroup'.to_le hBS
  have hBcard := moduleProduct_card_bound h B E D hBnorm
    hmodule hBfixE hBp (fun i => (hD i).2.2.1)
  have hJeqB : J = B := Subgroup.eq_of_le_of_card_ge hJB (by rwa [hJcard])
  have hEL : E = Subgroup.normalClosure (B : Set G) := by
    let L := Subgroup.normalClosure (B : Set G)
    have hJL : J ≤ L := hJeqB ▸ Subgroup.le_normalClosure
    apply le_antisymm
    · exact sup_le ((Subgroup.commutator_mono le_rfl hJL).trans
        (Subgroup.commutator_le_right _ L)) hJL
    · let : E.Normal := hE
      exact Subgroup.normalClosure_le_normal (hJeqB ▸ (show J ≤ E from le_sup_right))
  refine ⟨hJeqB, n, D, ?_⟩
  rw [← hEL]
  exact ⟨hprod.1, hprod, hDin, hD, hDN, hmodule⟩

end Stellmacher.SectionOne
