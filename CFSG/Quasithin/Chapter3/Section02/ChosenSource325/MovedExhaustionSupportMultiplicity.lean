module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportFixed
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.EndFieldRep
public import Theory.Representation.BinaryOffender.Homogeneous.Dimension
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Three natural copies in the commuting support orbit

The commuting component acts faithfully on every nonzero invariant subspace:
its quasisimple kernel is central, its odd-degree SL₃ marking removes that
center, and zero fixed space excludes the whole kernel. Its explicit
unitriangular element of order four therefore acts faithfully on the orbit
of the selected natural support seed.

That orbit is homogeneous for the support, since the generating component
commutes with it. If it had fewer than three copies, the proper seed would
give literal doubled coordinates. The commuting action then acts on a
two-dimensional space over the finite Schur field. In characteristic two,
an operator whose fourth power is one has square one on that space,
contradicting faithfulness of the original order-four element.

The actual Chapter12 application is
`SeedAlternativesMovedExhaustionSupportMultiplicity`. It supplies all orbit,
marking and fixed-space premises and gives the dimension bounds 9n on the
support orbit and 18n across the two original halves. Starred-actor movement,
the displacement estimates, Suzuki exclusion, U = W and Source325 assembly
remain with this owner.
Source: Aschbacher--Smith D.3.18 and the final D.3.10 multiplicity argument,
printed pp.203--204, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
set_option backward.isDefEq.respectTransparency false

private theorem square_of_fourth {F : Type*} [Field F] [CharP F 2]
    (u : Module.End F (Fin 2 → F)) (hu : u^4=1) : u^2=1 := by
  let : CharP (Module.End F (Fin 2 → F)) 2 := charP_of_injective_algebraMap' F 2
  have h4 : (u-1)^4=0 := by
    have h := sub_pow_char_pow_of_commute (R := Module.End F (Fin 2 → F)) 2 2
      (Commute.one_right u)
    simpa only [show 2^2=4 from rfl,hu,one_pow,sub_self] using h
  have hker := Module.End.ker_pow_le_ker_pow_finrank (u-1) 4
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,h4,LinearMap.ker_zero] at hker
  have h2 : (u-1)^2=0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hker)
  have h := sub_pow_char_of_commute (R := Module.End F (Fin 2 → F)) 2 (Commute.one_right u)
  rw [h2,one_pow] at h
  exact sub_eq_zero.mp h.symm

private theorem double_fourth_square
    {F D C E : Type*} [Field F] [CharP F 2]
    [Group D] [Group C] [AddCommGroup E] [Module F E] [Module (ZMod 2) E] [Nontrivial E]
    (σ : Representation (ZMod 2) D E)
    (hs : ∀ (f : E →ₗ[ZMod 2] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (ρ : Representation (ZMod 2) C (Fin 2 → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i))
    (a : C) (ha : a^4=1) : ρ (a^2)=1 := by
  classical
  obtain ⟨μ,he⟩ := ScalarMultiplicity.exists_multiplicity σ hs ρ hc
  have hm : μ (a^2) = 1 := by
    rw [map_pow]
    exact square_of_fourth (μ a) (by rw [←map_pow,ha,map_one])
  apply LinearMap.ext
  intro x
  change ρ (a^2) x = x
  have hex : x = ∑ i : Fin 2, Pi.single i (x i) := by ext i; simp
  conv_lhs => rw [hex,map_sum]
  apply Eq.trans _ hex.symm
  apply Finset.sum_congr rfl
  intro i _
  have hsng : (fun j => (Pi.single i (1 : F) : Fin 2 → F) j • x i) =
      Pi.single i (x i) := by
    ext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  rw [←hsng,he,hm]
  rfl

variable {D C E V : Type*} [Group D] [Group C]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem schur_double_fourth_square (σ : Representation (ZMod 2) D E) [IsIrreducible σ]
    (ρ : Representation (ZMod 2) C (E × E))
    (hc : ∀ a d x, ρ a (σ d x.1, σ d x.2) =
      (σ d (ρ a x).1, σ d (ρ a x).2))
    (a : C) (ha : a ^ 4 = 1) : ρ (a^2) = 1 := by
  classical
  let F := Module.End (ZMod 2)[D] σ.asModule
  let : Nontrivial σ.asModule := Subrepresentation.irreducible_module_nontrivial σ
  let : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  let σ' : Representation (ZMod 2) D σ.asModule :=
    (σ.asModuleEquiv.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp σ
  have hs (f : σ.asModule →ₗ[ZMod 2] σ.asModule)
      (hf : ∀ d v, f (σ' d v) = σ' d (f v)) :
      ∃ c : F, ∀ v, f v = c • v := by
    let q := σ.asModuleEquiv.toLinearMap.comp (f.comp σ.asModuleEquiv.symm.toLinearMap)
    have hq : ∀ d v, q (σ d v) = σ d (q v) := by
      intro d v
      exact congrArg σ.asModuleEquiv (hf d (σ.asModuleEquiv.symm v))
    exact ⟨IntertwiningMap.equivAlgEnd σ
      (q.intertwiningMap_of_isIntertwiningMap σ σ hq), fun v => rfl⟩
  let e : (E × E) ≃ₗ[ZMod 2] (Fin 2 → σ.asModule) :=
    (LinearEquiv.finTwoArrow (ZMod 2) E).symm.trans
      (LinearEquiv.piCongrRight fun _ => σ.asModuleEquiv.symm)
  let τ : Representation (ZMod 2) C (Fin 2 → σ.asModule) :=
    (e.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ
  have he (d : D) (x : E × E) :
      e (σ d x.1, σ d x.2) = fun i => σ' d (e x i) := by
    funext i
    fin_cases i <;> rfl
  have ht : ∀ a d x, τ a (fun i => σ' d (x i)) =
      fun i => σ' d (τ a x i) := by
    intro a d x
    change e (ρ a (e.symm (fun i => σ' d (x i)))) = _
    have hh : e.symm (fun i => σ' d (x i)) =
        (σ d (e.symm x).1, σ d (e.symm x).2) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    rw [hh,hc,he]
    rfl
  have hh := double_fourth_square σ' hs τ ht a ha
  apply LinearMap.ext
  intro x
  apply e.injective
  have hv := LinearMap.congr_fun hh (e x)
  change e (ρ (a^2) (e.symm (e x))) = e x at hv
  simpa only [e.symm_apply_apply,Module.End.one_apply] using hv

omit [FiniteDimensional (ZMod 2) V] in
private theorem coordinates_fourth_square (σ : Representation (ZMod 2) D E) [IsIrreducible σ]
    (α : Representation (ZMod 2) D V) (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (α d x) = α d (ρ a x))
    (e : α.Equiv (σ.prod σ)) (a : C) (ha : a ^ 4 = 1) : ρ (a^2) = 1 := by
  let τ : Representation (ZMod 2) C (E × E) :=
    (e.toLinearEquiv.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp ρ
  have he (d : D) (x : V) : e (α d x) = (σ d (e x).1, σ d (e x).2) :=
    LinearMap.congr_fun (e.isIntertwining' d) x
  have hh := schur_double_fourth_square σ τ (by
    intro a d x
    change e (ρ a (e.symm (σ d x.1,σ d x.2))) = _
    have hsym : e.symm (σ d x.1,σ d x.2) = α d (e.symm x) := by
      apply e.injective
      change e (e.symm (σ d x.1,σ d x.2)) = e (α d (e.symm x))
      rw [e.apply_symm_apply,he,e.apply_symm_apply]
    rw [hsym,hc,he]
    rfl) a ha
  ext x
  apply e.injective
  change e (ρ (a^2) x) = e x
  have hv := LinearMap.congr_fun hh (e x)
  change e (ρ (a^2) (e.symm (e x))) = e x at hv
  simpa only [e.symm_apply_apply,Module.End.one_apply] using hv


private theorem triple_degree_le_of_commuting_order_four
    (σ : Representation (ZMod 2) D V) (I : Subrepresentation σ)
    (hi : IsIrreducible I.toRepresentation) (hh : homogeneousPart I ⊤ = ⊤)
    (hp : I.toSubmodule ≠ ⊤)
    (ρ : Representation (ZMod 2) C V)
    (hc : ∀ a d x, ρ a (σ d x) = σ d (ρ a x))
    (a : C) (ha : a^4=1) (hne : ρ (a^2) ≠ 1) :
    3 * Module.finrank (ZMod 2) I.toSubmodule ≤ Module.finrank (ZMod 2) V := by
  by_contra! hd
  let := hi
  obtain ⟨e⟩ := double_coordinates_of_degree_le I hi hh hp
    (degree_le_double_of_lt_triple I hi hh hp hd)
  exact hne (coordinates_fourth_square I.toRepresentation σ ρ hc e a ha)


omit [FiniteDimensional (ZMod 2) V] in
private theorem homogeneous_of_commuting_orbit
    (σ : Representation (ZMod 2) D V) (τ : Representation (ZMod 2) C V)
    (hc : ∀ a d v, τ a (σ d v) = σ d (τ a v))
    (I : Subrepresentation σ) (hg : orbitSpan τ ⊤ I.toSubmodule = ⊤) :
    homogeneousPart I ⊤ = ⊤ := by
  apply top_unique
  conv_lhs => rw [←hg]
  apply iSup_le
  intro a
  let J : Subrepresentation σ := {
    toSubmodule := I.toSubmodule.map (τ a.val)
    apply_mem_toSubmodule := by
      intro d v hv
      obtain ⟨w,hw,rfl⟩ := hv
      exact ⟨σ d w,I.apply_mem_toSubmodule d hw,hc a.val d w⟩ }
  have he : SameModule I J := by
    refine ⟨I.toSubmodule.equivMapOfInjective (τ a.val) (apply_bijective τ a.val).injective,?_⟩
    intro d v
    exact Subtype.ext (hc a.val d v)
  exact le_iSup_of_le J (le_iSup_of_le ⟨le_top,he⟩ le_rfl)

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A commuting component with an order-four operator forces at least three
copies in the literal orbit of an irreducible support seed. -/
private theorem support_commuting_orbit_triple_degree
    (ρ : Representation (ZMod 2) H W) (X K : Subgroup H)
    (hc : K ≤ centralizer (X : Set H))
    (R : Submodule (ZMod 2) W) (hR : IsIrrPlus ρ X R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR.choose).toRepresentation)
    (hp : R < orbitSpan ρ K R)
    (a : K) (ha : a^4=1)
    (hne : ∃ v ∈ orbitSpan ρ K R, ρ (a.val^2) v ≠ v) :
    3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) := by
  let O := orbitSpan ρ K R
  have hXO : X ≤ subspaceStabilizer ρ O :=
    orbitSpan_component_invariant ρ (hc.trans (Subgroup.centralizer_le_normalizer _)) hR
  let U := invariantSubspace ρ X O hXO
  let I₀ := invariantSubspace ρ X R hR.choose
  let I := sectionLower (ρ.comp X.subtype) I₀ U
  let σ := U.toRepresentation
  let τ := (invariantSubspace ρ K O (orbitSpan_invariant ρ K R)).toRepresentation
  let e : I.toRepresentation.Equiv I₀.toRepresentation :=
    .mk (sectionLowerEquiv (ρ.comp X.subtype) hp.le) (by intro x; rfl)
  have hi' : IsIrreducible I.toRepresentation :=
    ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv
      (show ChapterB.QuasisimpleSource.ActionEquiv I.toRepresentation I₀.toRepresentation from
        ⟨MulEquiv.refl _,e.toLinearEquiv,fun x v => LinearMap.congr_fun (e.isIntertwining' x) v⟩) hi
  have hh : ∀ a x v, τ a (σ x v) = σ x (τ a v) := by
    intro a x v
    apply Subtype.ext
    change ρ a.val (ρ x.val v.val) = ρ x.val (ρ a.val v.val)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v.val) ((hc a.property x.val x.property).symm)
  have hg : orbitSpan τ ⊤ I.toSubmodule = ⊤ := by
    apply Submodule.map_injective_of_injective (f := O.subtype) Subtype.val_injective
    rw [orbitSpan_map_equivariant τ ρ K.subtype O.subtype (fun _ _ => rfl)]
    have hiO : I.toSubmodule.map O.subtype = R := by
      change (R.comap O.subtype).map O.subtype = R
      rw [Submodule.map_comap_subtype,inf_eq_right.mpr hp.le]
    rw [hiO,←MonoidHom.range_eq_map,Subgroup.range_subtype,Submodule.map_top,Submodule.range_subtype]
  have hip : I.toSubmodule ≠ ⊤ := by
    intro he
    apply hp.ne
    have hm := congrArg (Submodule.map O.subtype) he
    change (R.comap O.subtype).map O.subtype = (⊤ : Submodule (ZMod 2) O).map O.subtype at hm
    have hRO : R ≤ O := hp.le
    simpa only [Submodule.map_comap_subtype,inf_eq_right.mpr hRO,
      Submodule.map_top,Submodule.range_subtype] using hm
  have hn : τ (a^2) ≠ 1 := by
    intro he
    obtain ⟨v,hv,hn⟩ := hne
    exact hn (congrArg Subtype.val (LinearMap.congr_fun he (⟨v,hv⟩ : O)))
  have hd := triple_degree_le_of_commuting_order_four σ I hi'
    (homogeneous_of_commuting_orbit σ τ hh I hg) hip τ hh a ha hn
  rw [e.toLinearEquiv.finrank_eq] at hd
  exact hd

private theorem linearThree_order_four (F : ChapterB.QuasisimpleSource.BinaryField) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) F.Carrier, a^4=1 ∧ a^2≠1 := by
  let x : Matrix.PSL3Even.UnipotentGeometry.U F.Carrier := ⟨1,1,0⟩
  let f := Matrix.PSL3Even.UnipotentGeometry.specialLinear F.Carrier
  have h2 : x^2 ≠ 1 := by
    intro h
    have hh := (Matrix.PSL3Even.UnipotentGeometry.square_eq_one_iff F.Carrier x).mp h
    simp [x] at hh
  have h4 : x^4=1 := by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,pow_two,pow_two]
    apply Matrix.PSL3Even.UnipotentGeometry.U.ext <;> simp [x,CharTwo.add_self_eq_zero]
  exact ⟨f x,by rw [←map_pow,h4,map_one],fun h => h2
    (Matrix.PSL3Even.UnipotentGeometry.specialLinear_injective F.Carrier
      (by simpa only [map_pow,map_one] using h))⟩


/-- The same order-four obstruction bounds a whole homogeneous component.
The commuting SL₃ action is required to be faithful on that actual component. -/
theorem homogeneous_triple_degree_of_commuting_linearThree
    (σ : Representation (ZMod 2) D V) (I : Subrepresentation σ)
    (hi : IsIrreducible I.toRepresentation) (hh : homogeneousPart I ⊤ = ⊤)
    (hp : I.toSubmodule ≠ ⊤)
    (τ : Representation (ZMod 2) C V) (hf : Function.Injective τ)
    (hc : ∀ a d v, τ a (σ d v) = σ d (τ a v))
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : C ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    3 * Module.finrank (ZMod 2) I.toSubmodule ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨a,ha,ha2⟩ := linearThree_order_four F
  let b := e.symm a
  have hb : b^4=1 := by
    apply e.injective
    simpa only [b,map_pow,map_one,e.apply_symm_apply] using ha
  have hb2 : b^2≠1 := by
    intro he
    apply ha2
    simpa only [b,map_pow,map_one,e.apply_symm_apply] using congrArg e he
  exact triple_degree_le_of_commuting_order_four σ I hi hh hp τ hc b hb
    (fun he => hb2 (hf (he.trans τ.map_one.symm)))

/-- The original marked odd-degree SL₃ component supplies the order-four
operator on every nonzero invariant subspace. This discharges that premise
in the support-orbit multiplicity bound. -/
theorem support_commuting_linearThree_triple_degree
    (ρ : Representation (ZMod 2) H W) (X K : Subgroup H) [IsQuasisimple K]
    (hc : K ≤ centralizer (X : Set H)) (hfixed : fixedSpace ρ K = ⊥)
    (F : ChapterB.QuasisimpleSource.BinaryField) (ho : Odd F.degree)
    (eK : K ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (R : Submodule (ZMod 2) W) (hR : IsIrrPlus ρ X R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR.choose).toRepresentation)
    (hp : R < orbitSpan ρ K R) :
    3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (orbitSpan ρ K R) := by
  let O := orbitSpan ρ K R
  let τ := (invariantSubspace ρ K O (orbitSpan_invariant ρ K R)).toRepresentation
  have hz : center K = ⊥ := by
    have hSL : center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥ := by
      apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr
      rw [F.card_eq,Nat.BinaryTorusParity.two_pow_mod_three,Nat.odd_iff.mp ho]
      decide
    apply bot_unique
    intro k hk
    exact eK.injective ((hSL.le ((centerCongr eK) ⟨k,hk⟩).property).trans eK.map_one.symm)
  have hf : Function.Injective τ := by
    apply (MonoidHom.ker_eq_bot_iff τ).mp
    rcases IsQuasisimple.normal_le_center_or_eq_top τ.ker with hc | ht
    · exact bot_unique (hc.trans hz.le)
    · have hn : O = ⊥ := by
        apply bot_unique
        intro v hv
        apply hfixed.le
        intro k
        have hk : k ∈ τ.ker := ht.symm ▸ mem_top k
        exact congrArg Subtype.val (LinearMap.congr_fun hk (⟨v,hv⟩ : O))
      exact (hR.ne_bot ρ (bot_unique (hp.le.trans hn.le))).elim
  obtain ⟨a,ha,ha2⟩ := linearThree_order_four F
  let b := eK.symm a
  have hb : b^4=1 := by apply eK.injective; simpa only [b,map_pow,map_one,eK.apply_symm_apply] using ha
  have hb2 : b^2≠1 := by
    intro he
    apply ha2
    simpa only [b,map_pow,map_one,eK.apply_symm_apply] using congrArg eK he
  apply support_commuting_orbit_triple_degree ρ X K hc R hR hi hp b hb
  by_contra! hn
  apply hb2
  apply hf
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ρ (b.val^2) v.val = ρ 1 v.val
  simpa only [map_one,Module.End.one_apply] using hn v.val v.property

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
