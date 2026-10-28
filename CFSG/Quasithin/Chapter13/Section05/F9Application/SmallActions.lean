module

public import CFSG.Quasithin.Chapter13.Section05.F9Application.PointCore
public import Theory.GroupTheory.MutualBinaryActions
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
/-!
# Symmetric small actions and the source commutator lift

The range of the actual permutation action equals the relative centralizer
index. Conjugation transports the inverse-conjugate index to the reverse
action, so two action bounds of order at most two force the literal
commutator [V,Vᵍ] to have order at most two. Natural orthogonality then
rules out a nontrivial seed commutator contained in the original line.
Applying the same argument to g⁻¹ gives both conclusions of F.9.1(e).

The source antecedents construct the two relative-normalizer placements.
The action bounds remain the genuine earlier plane-fusion obligation from
13.5.6; no F9 applicability or desired seed-centrality premise is used.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem permutation_range_card (X:Subgroup G)
    (hX:X≤localModuleNormalizer (M:=M) (V:=V)) :
    Nat.card ((permutation d).comp (inclusion hX)).range=
      (centralizer (V:Set G)).relIndex X := by
  let f: X→*Equiv.Perm (Fin 6):=(permutation d).comp (inclusion hX)
  let a: X→*MulAut V:=V.normalizerMonoidHom.comp (inclusion (hX.trans inf_le_right))
  have hk:f.ker=a.ker := by
    ext x
    change f x=1 ↔ a x=1
    constructor
    · intro hx
      ext v : 1
      apply d.coordinate.injective
      apply Multiplicative.toAdd.injective
      have hc:=conjugation d (inclusion hX x) v
      change (d.coordinate (a x v)).toAdd=
        naturalRepresentation (Fin 6) (f x) (d.coordinate v).toAdd at hc
      simpa [hx] using hc
    · intro hx
      apply naturalRepresentation_injective (Fin 6) (by decide)
      rw [map_one]
      ext w : 1
      obtain ⟨v,hv⟩:=d.coordinate.surjective (Multiplicative.ofAdd w)
      have hv':(d.coordinate v).toAdd=w:=hv
      rw [←hv']
      change naturalRepresentation (Fin 6) (permutation d (inclusion hX x)) (d.coordinate v).toAdd=_
      rw [←conjugation d (inclusion hX x)]
      exact congrArg (fun v:V=>(d.coordinate v).toAdd) (DFunLike.congr_fun hx v)
  change Nat.card f.range=_
  rw [←index_ker,hk,index_ker]
  exact normalizer_action_range_card V X (hX.trans inf_le_right)

omit d [Finite G] in
private theorem centralizer_map_equiv (A:Subgroup G) (e:G≃*G) :
    (centralizer (A:Set G)).map e.toMonoidHom=centralizer (A.map e.toMonoidHom:Set G) := by
  ext g
  rw [mem_map_equiv]
  constructor
  · intro hg a ha
    obtain ⟨b,hb,rfl⟩:=ha
    have hh:=congrArg e (hg b hb)
    change e b*g=g*e b
    simpa only [map_mul,e.apply_symm_apply] using hh
  · intro hg a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hg (e a) (mem_map_of_mem _ ha)

theorem conjugate_commutator_card_le_two (g:G)
    (hg:V.map (MulAut.conj g).toMonoidHom≤localModuleNormalizer (M:=M) (V:=V))
    (hgi:V.map (MulAut.conj g⁻¹).toMonoidHom≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hsmall:Nat.card (conjugateAction d g hg).range≤2)
    (hsmalli:Nat.card (conjugateAction d g⁻¹ hgi).range≤2) :
    Nat.card (⁅V,V.map (MulAut.conj g).toMonoidHom⁆:Subgroup G)≤2 := by
  let := elementary d
  apply commutator_card_le_two_of_mutual_centralizer_indices V _
    (hg.trans inf_le_right) (le_normalizer_iff_commutator_le_right.mpr (hcomm.trans inf_le_right))
  · rwa [←permutation_range_card d _ hg]
  · have he:(V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom=V := by
      rw [map_map]
      have hh:(MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom=MonoidHom.id G := by
        ext x : 1
        change g*(g⁻¹*x*(g⁻¹)⁻¹)*g⁻¹=x
        group
      rw [hh,map_id]
    have ht:=relIndex_map_map_of_injective (f:=(MulAut.conj g).toMonoidHom) (centralizer (V:Set G))
      (V.map (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g).injective
    rw [centralizer_map_equiv,he] at ht
    rw [ht,←permutation_range_card d _ hgi]
    exact hsmalli

theorem local_centralizes_seed_of_commutator_le_line (X:Subgroup G)
    (hX:X≤localModuleNormalizer (M:=M) (V:=V)) (hc:⁅V,X⁆≤V₁) :
    X≤centralizer (V₃:Set G) := by
  intro x hx
  let a:localModuleNormalizer (M:=M) (V:=V):=⟨x,hX hx⟩
  have hd:∀w,naturalRepresentation (Fin 6) (permutation d a) w-w∈
      form.orthogonal (image d V₃) := by
    intro w
    rw [seed_perpendicular d,LinearMap.BilinForm.orthogonal_orthogonal
      form_nondegenerate form_alt.isRefl]
    have hm:naturalRepresentation (Fin 6) (permutation d a) w-w∈image d ⁅V,X⁆ := by
      rw [image_commutator_self d X hX]
      exact Submodule.subset_span ⟨_,⟨⟨x,hx⟩,rfl⟩,w,Submodule.mem_top,rfl⟩
    obtain ⟨v,hv,he⟩:=(mem_image d ⁅V,X⁆ _).mp hm
    exact (mem_image d V₁ _).mpr ⟨v,hc hv,he⟩
  have hf:=(fixes_iff_displacement (permutation d a) (image d V₃)).mpr hd
  apply mem_centralizer_iff.mpr
  intro v hv
  let vV:V:=⟨v,d.seed_le hv⟩
  have hh:=hf (d.coordinate vV).toAdd ((mem_image d V₃ _).mpr ⟨vV,hv,rfl⟩)
  rw [←conjugation d a vV] at hh
  have he:=congrArg Subtype.val (d.coordinate.injective hh)
  change x*v*x⁻¹=v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
/-- An order-two commutator cannot move the seed merely inside the line. -/
theorem local_seed_commutator_eq_bot (X:Subgroup G)
    (hX:X≤localModuleNormalizer (M:=M) (V:=V))
    (hcard:Nat.card (⁅V,X⁆:Subgroup G)≤2) (hseed:⁅V₃,X⁆≤V₁) :
    ⁅V₃,X⁆=⊥ := by
  by_contra hn
  have hdiv:Nat.card (⁅V₃,X⁆:Subgroup G)∣2 := d.line_card ▸ card_dvd_of_le hseed
  have htwo:Nat.card (⁅V₃,X⁆:Subgroup G)=2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdiv with he|he
    · exact (hn (card_eq_one.mp he)).elim
    · exact he
  have he:⁅V₃,X⁆=V₁ := eq_of_le_of_card_ge hseed (by rw [htwo,d.line_card])
  have hline:V₁≤⁅V,X⁆ := he.symm.le.trans (commutator_mono d.seed_le le_rfl)
  have hfull:⁅V,X⁆=V₁ := (eq_of_le_of_card_ge hline (by rwa [d.line_card])).symm
  have hcentral:=local_centralizes_seed_of_commutator_le_line d X hX hfull.le
  exact hn (commutator_comm V₃ X ▸ commutator_eq_bot_iff_le_centralizer.mpr hcentral)

theorem inverse_seed_commutator_le_line (g:G) (hg:g∈G₁)
    (hseed:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁) :
    ⁅V₃,V.map (MulAut.conj g⁻¹).toMonoidHom⁆≤V₁ := by
  have hi:=map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hseed
  rw [map_commutator] at hi
  change ⁅(V₃.conjBy g).conjBy g⁻¹,V.conjBy g⁻¹⁆≤V₁.conjBy g⁻¹ at hi
  rw [conjBy_inv] at hi
  have hfix:V₁.conjBy g⁻¹=V₁ :=
    mem_normalizer_iff_map_conj_eq.mp (d.first_normalizer ▸ G₁.inv_mem hg)
  rwa [hfix] at hi

/-- Both literal F9(e) conclusions from the symmetric small-action bounds.
Their separate plane-fusion source producer remains explicit. -/
theorem seed_commutator_lifting_of_small_actions (g:G) (hg:g∈G₁)
    (hp:V.map (MulAut.conj g).toMonoidHom≤localModuleNormalizer (M:=M) (V:=V))
    (hpi:V.map (MulAut.conj g⁻¹).toMonoidHom≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hseed:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hsecond:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁)
    (hsmall:Nat.card (conjugateAction d g hp).range≤2)
    (hsmalli:Nat.card (conjugateAction d g⁻¹ hpi).range≤2) :
    ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆=⊥ ∧
      ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆=⊥ := by
  have hcard:=conjugate_commutator_card_le_two d g hp hpi hcomm hsmall hsmalli
  refine ⟨local_seed_commutator_eq_bot d _ hp hcard hseed,?_⟩
  have he:(⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆).map
      (MulAut.conj g).toMonoidHom=⁅V,V.map (MulAut.conj g).toMonoidHom⁆ := by
    rw [map_commutator]
    change ⁅V.conjBy g,(V.conjBy g⁻¹).conjBy g⁆=⁅V,V.conjBy g⁆
    rw [conjBy_inv',commutator_comm]
  have hcardi:Nat.card (⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆:Subgroup G)≤2 := by
    have hm:=card_map_of_injective (K:=⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆)
      (f:=(MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [he] at hm
    exact hm ▸ hcard
  have hi:=local_seed_commutator_eq_bot d _ hpi hcardi
    (inverse_seed_commutator_le_line d g hg hsecond)
  have hm:=congrArg (fun A:Subgroup G=>A.map (MulAut.conj g).toMonoidHom) hi
  rw [map_commutator,Subgroup.map_bot] at hm
  change ⁅V₃.conjBy g,(V.conjBy g⁻¹).conjBy g⁆=⊥ at hm
  rwa [conjBy_inv'] at hm

/-- The original source antecedents construct both placements; only the
rank-one bound left by the earlier plane-fusion argument is required. -/
theorem source_lifting_of_small_actions (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hseed:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hsecond:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁)
    (hsmall:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hseed)).range≤2)
    (hsmalli:Nat.card (conjugateAction d g⁻¹
      (conjugate_le_local d g⁻¹ (G₁.inv_mem hg) hc
        (inverse_seed_commutator_le_line d g hg hsecond))).range≤2) :
    ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆=⊥ ∧
      ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆=⊥ :=
  seed_commutator_lifting_of_small_actions d g hg _ _ hcomm hseed hsecond hsmall hsmalli

end CFSG.Quasithin.Chapter13.Section05.QuadraticSource
