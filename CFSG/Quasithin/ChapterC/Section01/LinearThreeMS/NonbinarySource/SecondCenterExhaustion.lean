module
public import Theory.Representation.SL3.DualLiftCenter
public import Theory.GroupTheory.PGroup.SecondCenterExhaustion
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterImage

/-!
# Exhausting the core from its second central section

A doubled-dual subsection over a whole natural or doubled-natural center has
exactly that center whenever its full preimage is nonabelian. The proof keeps
one full SL₃ marking, transports all dual diagonals to their literal preimages,
and applies the invariant-line and square-map arguments from DualLiftCenter.

For the second central section, this center identity forces Z₂(Q)=Q by
SecondCenterExhaustion. Thus recognizing a nonabelian doubled-dual second
central section also recognizes the whole Q/Z(Q). No class-two assumption,
trivial covering kernel, or deletion of a central summand is used.

NonblockSecondCenterExhaustion applies this criterion to the original source
and constructs its third alternative and MSData from the smaller section.
Existence of the upper model, exclusion of the elementary upper branch and
the nonabelian doubled-center branch, and the general fixed-factor row remain
unproved. Source: Aschbacher–Smith C.1.34–35, printed pp.136–138; MS93 Section 4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterExhaustion
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open SecondCenterSections
variable {G : Type*} [Group G] {K Q A : Subgroup G}
variable {F : Type} [Field F] [CharP F 2]
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "T₂" => Subgroup.upperCentralSeries Q 2

private theorem subsection_elementary_or_center {W : Type*} [AddCommGroup W] [Module F W]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hAQ : A≤Q)
    (ρ : Representation F SL(3,F) W)
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) ρ)
    (hA : HasSectionModel K A Z (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual))
    (hfix : ∀ f : Module.Dual F (Fin 3 → F), f≠0 → ∀ w : W,
      (∀ g : SL(3,F), (specialLinearNatural 3).dual g f=f → ρ g w=w) → w=0)
    : IsElementaryAbelian 2 A ∨
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn A=Z := by
  obtain ⟨hZA,hKA,_,hi,d,hd⟩ := hA
  let := hi
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hi₀,c₀,hc₀⟩ := hm
  let := hi₀
  let c : Z ≃* Multiplicative W := QuotientGroup.quotientBot.symm.trans c₀
  let p := d.toMonoidHom.comp (QuotientGroup.mk' ((Z).subgroupOf A))
  have hk : p.ker=(Z).subgroupOf A := by
    ext x
    change d (QuotientGroup.mk' _ x)=1 ↔ (x:G)∈Z
    rw [d.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let u : p.ker ≃* Multiplicative W :=
    ((MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hZA)).trans c
  let act : K →* MulAut A := A.normalizerMonoidHom.comp (inclusion hKA)
  have hα : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker ≤ center A := by
    intro x hx
    have hxZ : (x:G)∈Z := (show x∈(Z).subgroupOf A from hk ▸ hx)
    obtain ⟨z,hz,hzx⟩ := hxZ
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y:G)*(x:G)=(x:G)*(y:G)
    rw [←hzx]
    exact congrArg Q.subtype (mem_center_iff.mp hz (⟨y,hAQ y.property⟩:Q))
  have hp : Function.Surjective p := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have he (k : K) (x : A) : (p (act k x)).toAdd=
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual)
        (linearThreeActor e k) (p x).toAdd := hd k x (act k x) rfl
  have hu (k : K) (x y : p.ker) (hy : (y:A)=act k (x:A)) :
      (u y).toAdd=ρ (linearThreeActor e k) (u x).toAdd := by
    apply hc₀ k ((subgroupOfEquivOfLe hZA) ((MulEquiv.subgroupCongr hk) x))
      ((subgroupOfEquivOfLe hZA) ((MulEquiv.subgroupCongr hk) y))
    exact congrArg (fun z : A => (z:G)) hy
  have hel := SL3ParabolicNatural.dual_lines_elementary_of_fixed_zero
    (linearThreeActor e) hα act p hker ρ u he hu hfix
  by_cases hab : IsMulCommutative A
  · exact Or.inl (SL3ParabolicNatural.elementary_of_abelian_dual_lines p hp hel hab)
  right
  have hc := SL3ParabolicNatural.center_eq_kernel_of_elementary_dual_lines
    (linearThreeActor e) hα act p hp hker he hel hab
  change (center A).map A.subtype=Z
  rw [hc,hk,map_subgroupOf_eq_of_le hZA]

/-- A doubled-dual subsection over a whole natural or doubled center is
 elementary, or has exactly that center. Both central summands are retained. -/
theorem doubled_dual_subsection_alternatives
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hAQ : A≤Q)
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K Z ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hA : HasSectionModel K A Z (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual)) :
    IsElementaryAbelian 2 A ∨
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn A=Z := by
  rcases hm with hm|hm
  · exact subsection_elementary_or_center e hAQ _ hm hA SL3ParabolicNatural.dual_stabilizer_fixed_zero
  · apply subsection_elementary_or_center e hAQ _ hm hA
    intro f hf w hw
    exact Prod.ext
      (SL3ParabolicNatural.dual_stabilizer_fixed_zero f hf w.1
        (fun g hg => congrArg Prod.fst (hw g hg)))
      (SL3ParabolicNatural.dual_stabilizer_fixed_zero f hf w.2
        (fun g hg => congrArg Prod.snd (hw g hg)))

variable [Finite G]

omit [Finite G] in
/-- The intrinsic and ambient second centers have the same embedded center. -/
private theorem second_center_center_map :
    ((center T₂).map (T₂).subtype).map Q.subtype =
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (secondCenterIn Q) := by
  let j : T₂ ≃* secondCenterIn Q := (T₂).equivMapOfInjective Q.subtype Q.subtype_injective
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨j z,(centerCongr j ⟨z,hz⟩).property,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    let z := (centerCongr j).symm ⟨y,hy⟩
    refine ⟨(z:T₂),⟨(z:T₂),z.property,rfl⟩,?_⟩
    exact congrArg (fun w : center (secondCenterIn Q) => ((w:secondCenterIn Q):G))
      ((centerCongr j).apply_symm_apply ⟨y,hy⟩)

/-- The doubled-dual second central section is elementary or exhausts the
core. The common marking and the full central kernel are unchanged. -/
theorem second_elementary_or_core_of_double_dual
    (hQ : IsPGroup 2 Q) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K Z ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hupper : HasSectionModel K (secondCenterIn Q) Z (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual))
    : IsElementaryAbelian 2 (secondCenterIn Q) ∨
      (secondCenterIn Q=Q ∧ HasSectionModel K Q Z (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual)) := by
  obtain hel|hc := doubled_dual_subsection_alternatives e (map_subtype_le _) hm hupper
  · exact Or.inl hel
  right
  have hi : IsElementaryAbelian 2 (center Q) := by
    rcases hm with hm|hm
    · exact (SecondCenterSquares.exists_marked_squares _ _ hm).1
    · exact (SecondCenterSquares.exists_marked_squares _ _ hm).1
  let := hi
  have hci : (center T₂).map (T₂).subtype=center Q := by
    apply map_injective Q.subtype_injective
    rw [second_center_center_map]
    exact hc
  have ht := SecondCenterFrattini.second_eq_top_of_center_eq hQ hci
  have he : secondCenterIn Q=Q := by
    unfold secondCenterIn
    rw [ht,←MonoidHom.range_eq_map,range_subtype]
  exact ⟨he,by simpa only [he] using hupper⟩

/-- A nonabelian second center with doubled-dual central quotient is already
the whole core. The common marking and full central kernel are unchanged. -/
theorem second_eq_core_of_nonabelian_double_dual
    (hQ : IsPGroup 2 Q) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K Z ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hupper : HasSectionModel K (secondCenterIn Q) Z (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual))
    (hna : ¬IsMulCommutative (secondCenterIn Q)) :
    secondCenterIn Q=Q ∧ HasSectionModel K Q Z (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).dual.prod (specialLinearNatural 3).dual) := by
  exact (second_elementary_or_core_of_double_dual hQ e hm hupper).resolve_left
    (fun hel => hna hel.toIsMulCommutative)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterExhaustion
