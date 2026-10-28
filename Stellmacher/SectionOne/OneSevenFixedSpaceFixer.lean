module
public import Stellmacher.SectionOne.OneSevenBaumann
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# The pointwise fixer of the one-seven fixed space

For the faithful elementary two-group action of Section One and the supplied
Sylow S, the pointwise fixer of C_V(J(V,S)) is exactly J(V,S). The public
interface retains the vanishing E-fixed complement required by the intended
Section Eight application; the proof also handles a nontrivial complement,
since every pointwise fixer of C_V(J) already fixes C_V(E).

The global one-seven product is normal, and J is its Sylow intersection.
Each factor is therefore normalized by J. The fixed-space normalizer theorem
makes every pointwise fixer of C_V(J) preserve each factor and its four-element
support. The two-group J has a nonidentity fixed vector on each support, and
every element of the pointwise fixer fixes that vector. The automorphism group
of a group of order four fixing a nonidentity vector has order at most two.

The module decomposition and ambient faithfulness embed the pointwise fixer
into the product of these support-action images, because it also fixes the
common E-fixed complement. Its order is consequently at most 2^n, the exact
order of the n factor Sylows generating J. The defining inclusion of J in its
fixed-space fixer gives equality. All actions are restrictions of the original
supplied action; no actor two-group assumption is imposed on the fixer.

This is the natural-factor fixed-space consequence of Stellmacher (1.7),
Journal of Algebra 190 (1997), p.19, used in (8.4)(8)--(9), pp.39--40,
refs/files/stellmacher-n-group.pdf. Statements about a selected factor's
commutator support are separate from this pointwise-fixer identification.
-/

namespace Stellmacher.SectionOne
universe u

private theorem fixed_support_card_bound
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (B E : Subgroup G) {n : ℕ} (D : Fin n → Subgroup G)
    (hnorm : ∀ i, B ≤ Subgroup.normalizer (D i : Set G))
    (hmodule : IsInternalDirectProductFamily (⊤ : Subgroup V)
      (fun i : Option (Fin n) => match i with
        | none => FixedPoints.subgroup E V
        | some i => commutatorAction (D i) V))
    (hfix : B ≤ fixingSubgroup G (FixedPoints.subgroup E V : Set V))
    (hU : ∀ i, Nat.card (commutatorAction (D i) V) = 4)
    (hpoint : ∀ i, ∃ z : commutatorAction (D i) V, z ≠ 1 ∧
      ∀ b ∈ B, b • (z : V) = z) :
    Nat.card B ≤ 2 ^ n := by
  classical
  let U (i : Fin n) : Subgroup V := commutatorAction (D i) V
  let _ (i : Fin n) : IsInvariant B V (U i) :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor B (D i) (hnorm i)
  let ρ (i : Fin n) : B →* MulAut (U i) := MulDistribMulAction.toMulAut B (U i)
  let f : B →* (∀ i, (ρ i).range) := MonoidHom.pi fun i => (ρ i).rangeRestrict
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro b hb
      have hbfix (i : Fin n) (v : V) (hv : v ∈ U i) : (b : G) • v = v := by
        have hρ : ρ i b = 1 := congrArg Subtype.val (congrFun (MonoidHom.mem_ker.mp hb) i)
        have hact := MulEquiv.congr_fun hρ (⟨v, hv⟩ : U i)
        exact congrArg Subtype.val hact
      have hbV : ∀ v : V, (b : G) • v = v := by
        intro v
        have hv : v ∈ (⊤ : Subgroup V) := Subgroup.mem_top v
        rw [hmodule.1, Subgroup.iSup_eq_closure] at hv
        refine Subgroup.closure_induction (p := fun v _ => (b : G) • v = v)
          ?_ ?_ ?_ ?_ hv
        · intro x hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          cases i with
          | none => exact (mem_fixingSubgroup_iff (M := G)).mp (hfix b.property) x hi
          | some i => exact hbfix i x hi
        · exact smul_one b.val
        · intro x y _ _ hx hy
          rw [smul_mul', hx, hy]
        · intro x _ hx
          rw [smul_inv', hx]
      have hbG : (b : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        exact fun v _ => hbV v
      rw [h.action_faithful] at hbG
      exact Subtype.ext hbG
    · exact bot_le
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_pi] at hcard
  have hle : ∏ i : Fin n, Nat.card (ρ i).range ≤ ∏ _i : Fin n, 2 := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i hi
    obtain ⟨z,hzne,hzfix⟩ := hpoint i
    exact card_mulAut_subgroup_le_two_of_fixed_point (hU i) z hzne (ρ i).range (by
      rintro f ⟨b,rfl⟩
      exact Subtype.ext (hzfix b b.property))
  exact hcard.trans (by simpa using hle)


/-- J is the entire pointwise fixer of its fixed space, including when its fixed complement is nontrivial. -/
public theorem oneSeven_fixedSpace_fixer_eq_oneJ_unconditional
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    fixingSubgroup G (FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V : Set V) =
      oneJ (V := V) (S : Subgroup G) := by
  classical
  let J := oneJ (V := V) (S : Subgroup G)
  let B := fixingSubgroup G (FixedPoints.subgroup J V : Set V)
  let E := oneSevenGenerated (G := G) (V := V)
  let F := oneSevenFactors (G := G) (V := V)
  obtain ⟨hEnormal,hprod,hJE⟩ := oneSeven_global_product h S
  obtain ⟨hJid,_⟩ := oneSeven_global_identification h S
  change J = (S : Subgroup G) ⊓ E at hJid
  change IsInternalDirectProduct E F at hprod
  have hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D :=
    fun D hD => (mem_oneSevenFactors_iff D).mp hD
  have hJleS : J ≤ (S : Subgroup G) := by rw [hJid]; exact inf_le_left
  have hJp : IsPGroup 2 J := S.isPGroup'.to_le hJleS
  have hJcard : Nat.card J = 2 ^ F.card := by
    rw [hJid]
    exact (sl2_product_sylow_coordinates S E hEnormal F hprod
      (fun D hD => (hF D hD).1)).2.2.1
  have hJB : J ≤ B := by
    intro j hj
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact hv ⟨j,hj⟩
  have hBfix : B ≤ fixingSubgroup G (FixedPoints.subgroup E V : Set V) := by
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply (mem_fixingSubgroup_iff (M := G)).mp hb v
    intro j
    exact hv ⟨j,hJE j.property⟩
  let I := {D : Subgroup G // D ∈ F}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup G := fun i => (eI i).val
  have hDi (i : Fin n) : D i ∈ F := (eI i).property
  have hinj : Function.Injective D := by
    intro i j hij
    exact eI.injective (Subtype.ext hij)
  have hgen : E = ⨆ i : Fin n, D i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro K
      obtain ⟨i,rfl⟩ := eI.surjective K
      exact le_iSup D i
    · apply iSup_le
      intro i
      exact le_iSup (fun K : I => (K : Subgroup G)) (eI i)
  have hnormJ (i : Fin n) : J ≤ Subgroup.normalizer (D i : Set G) := by
    have hDE : D i ≤ E := by rw [hgen]; exact le_iSup D i
    exact hJE.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp
      (hprod.2.1 (D i) (hDi i)))
  have hnormB (i : Fin n) : B ≤ Subgroup.normalizer (D i : Set G) :=
    oneSevenFactor_fixedSpace_normalizes h (D i) J (hF (D i) (hDi i)) hJp (hnormJ i)
  have hpoints (i : Fin n) : ∃ z : commutatorAction (D i) V, z ≠ 1 ∧
      ∀ b ∈ B, b • (z : V) = z := by
    let U := commutatorAction (D i) V
    let _ : IsInvariant J V U := commutatorAction_isInvariant_of_normalizing_actor J (D i) (hnormJ i)
    have hdiv : 2 ∣ Nat.card U := by rw [show Nat.card U = 4 from (hF (D i) (hDi i)).2.2.1]; decide
    have hone : (1 : U) ∈ MulAction.fixedPoints J U := by
      rw [MulAction.mem_fixedPoints]
      intro j
      exact smul_one j
    obtain ⟨z,hz,hzne⟩ := hJp.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdiv hone
    refine ⟨z,Ne.symm hzne,?_⟩
    intro b hb
    apply (mem_fixingSubgroup_iff (M := G)).mp hb z
    intro j
    exact congrArg Subtype.val (hz j)
  have hbound := fixed_support_card_bound h B E D hnormB
    (oneSevenFactor_module_product h D (fun i => hF (D i) (hDi i)) hinj E hgen)
    hBfix (fun i => (hF (D i) (hDi i)).2.2.1) hpoints
  have hcard : Nat.card B ≤ Nat.card J := by
    rw [hJcard]
    simpa only [n,I,Fintype.card_coe] using hbound
  exact (Subgroup.eq_of_le_of_card_ge hJB hcard).symm
/-- The fixed-complement-free interface for the Section Eight application. -/
public theorem oneSeven_fixedSpace_fixer_eq_oneJ
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (_hfixed : FixedPoints.subgroup (oneE (V := V) (S : Subgroup G)) V = ⊥) :
    fixingSubgroup G (FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V : Set V) =
      oneJ (V := V) (S : Subgroup G) :=
  oneSeven_fixedSpace_fixer_eq_oneJ_unconditional h S
end Stellmacher.SectionOne
