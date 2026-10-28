module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLiftKernel
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Group

/-!
# Actual commutator rows for the canonical perfect lift

The original section kernel inside the canonical perfect lift pairs with
F into the literal denominator D. Because the lift centralizes D, the
pairing descends through the supplied F/D coordinates to equivariant
commutator rows. Their kernel is exactly the full-F centralizer, and their
evaluations generate precisely the actual commutator subgroup [B,F].
No equality between that subgroup and all of D is assumed.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v

private theorem exists_central_section_rows
    {G : Type*} [Group G] (H F D L B : Subgroup G)
    [IsMulCommutative F] [IsMulCommutative D]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (dF : BinaryConjugationSection H F D ρ)
    (hLH : L ≤ H) (hBD : B ≤ centralizer (D : Set G))
    (hLD : L ≤ centralizer (D : Set G))
    (hcomm : ⁅B,F⁆ ≤ D) :
    let ψ := ρ.comp (Subgroup.inclusion hLH)
    ∃ row : B →* (Multiplicative W →* D),
      (∀ (b : B) (f : F), (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆) ∧
      row.ker = (centralizer (F : Set G)).subgroupOf B ∧
      (∀ (l : L) (b b' : B), (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        ∀ w : W, row b' (Multiplicative.ofAdd w) =
          row b (Multiplicative.ofAdd (ψ l⁻¹ w))) ∧
      (⨆ b : B, (row b).range).map D.subtype = ⁅B,F⁆ := by
  let ψ := ρ.comp (Subgroup.inclusion hLH)
  have hDF : D ≤ centralizer (F : Set G) := dF.kernel_le.trans F.le_centralizer
  let raw (b : B) : F →* D := centralCommutatorHom F D hDF b
    (fun f hf => hcomm (commutator_mem_commutator b.property hf))
  have hkill (b : B) : dF.coordinates.ker ≤ (raw b).ker := by
    intro f hf
    rw [dF.kernel_eq] at hf
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hBD b.property f hf).symm
  let row₀ (b : B) : Multiplicative W →* D :=
    dF.coordinates.liftOfSurjective dF.onto ⟨raw b,hkill b⟩
  have happly (b : B) (f : F) : (row₀ b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆ := by
    change ((dF.coordinates.liftOfSurjective dF.onto ⟨raw b,hkill b⟩)
      (dF.coordinates f) : G) = _
    rw [dF.coordinates.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv dF.onto)]
    rfl
  let row : B →* (Multiplicative W →* D) := {
    toFun := row₀
    map_one' := by
      apply MonoidHom.ext
      intro w
      obtain ⟨f,rfl⟩ := dF.onto w
      apply Subtype.ext
      rw [happly]
      change ⁅(1 : G),(f : G)⁆ = 1
      exact commutatorElement_one_left (f : G)
    map_mul' := by
      intro a b
      apply MonoidHom.ext
      intro w
      obtain ⟨f,rfl⟩ := dF.onto w
      apply Subtype.ext
      change (row₀ (a*b) (dF.coordinates f) : G) =
        (row₀ a (dF.coordinates f) : G) * (row₀ b (dF.coordinates f) : G)
      rw [happly,happly,happly]
      have hc := hcomm (commutator_mem_commutator b.property f.property)
      have ha : (a : G) * ⁅(b : G),(f : G)⁆ = ⁅(b : G),(f : G)⁆ * (a : G) :=
        (hBD a.property _ hc).symm
      change ⁅(a : G) * (b : G),(f : G)⁆ = ⁅(a : G),(f : G)⁆ * ⁅(b : G),(f : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,ha,mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (raw b f) (raw a f)) }
  have heval (b : B) (f : F) : (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆ := happly b f
  refine ⟨row,heval,?_,?_,?_⟩
  · ext b
    constructor
    · intro hb f hf
      have he := congrArg (fun q : Multiplicative W →* D =>
        (q (dF.coordinates ⟨f,hf⟩) : G)) (MonoidHom.mem_ker.mp hb)
      rw [heval] at he
      exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
    · intro hb
      apply MonoidHom.mem_ker.mpr
      apply MonoidHom.ext
      intro w
      obtain ⟨f,rfl⟩ := dF.onto w
      apply Subtype.ext
      rw [heval]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hb f f.property).symm
  · intro l b b' hb' w
    have hcov (z : W) : row b' (Multiplicative.ofAdd (ψ l z)) = row b (Multiplicative.ofAdd z) := by
      obtain ⟨f,hf⟩ := dF.onto (Multiplicative.ofAdd z)
      let f' : F := ⟨(l : G) * (f : G) * (l : G)⁻¹,
        le_normalizer_iff.mp dF.normalized l (hLH l.property) f f.property⟩
      have hf' : dF.coordinates f' = Multiplicative.ofAdd (ψ l z) := by
        apply Multiplicative.toAdd.injective
        have hh := dF.equivariant (Subgroup.inclusion hLH l) f
        change (dF.coordinates f').toAdd = ψ l (dF.coordinates f).toAdd at hh
        simpa only [hf,toAdd_ofAdd] using hh
      apply Subtype.ext
      rw [←hf',←hf,heval,heval,hb']
      change ⁅(l : G) * (b : G) * (l : G)⁻¹,
        (l : G) * (f : G) * (l : G)⁻¹⁆ = ⁅(b : G),(f : G)⁆
      have hc : (l : G) * ⁅(b : G),(f : G)⁆ = ⁅(b : G),(f : G)⁆ * (l : G) :=
        (hLD l.property _ (hcomm (commutator_mem_commutator b.property f.property))).symm
      calc
        _ = (l : G) * ⁅(b : G),(f : G)⁆ * (l : G)⁻¹ := by group
        _ = _ := by rw [hc,mul_inv_cancel_right]
    have hinv : ψ l (ψ l⁻¹ w) = w := by
      change (ψ l * ψ l⁻¹) w = w
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
    simpa only [hinv] using hcov (ψ l⁻¹ w)
  · apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply iSup_le
      intro b
      rintro _ ⟨w,rfl⟩
      obtain ⟨f,rfl⟩ := dF.onto w
      change (row b (dF.coordinates f) : G) ∈ ⁅B,F⁆
      rw [heval]
      exact commutator_mem_commutator b.property f.property
    · apply commutator_le.mpr
      intro b hb f hf
      refine ⟨row ⟨b,hb⟩ (dF.coordinates ⟨f,hf⟩),?_,heval _ _⟩
      exact (le_iSup (fun x : B => (row x).range) ⟨b,hb⟩) ⟨_,rfl⟩

variable {G : Type u} [Group G] [Finite G]

/-- The canonical perfect lift supplies actual equivariant commutator rows
on the caller's unchanged F/D coordinates, with their exact centralizer
kernel and literal generated commutator subgroup. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_kernel_rows
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
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let B := K ⊓ L
          let hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
          let ψ := ρ.comp (Subgroup.inclusion hLMc)
          Group.IsPerfect L ∧ L ≤ normalizer (B : Set G) ∧
            L ≤ centralizer (D : Set G) ∧ ⁅F,L⁆ = F ∧ ⁅B,F⁆ ≤ D ∧
            ∃ heD : IsElementaryAbelian 2 D,
              letI := heD
              ∃ row : B →* (Multiplicative W →* D),
                (∀ (b : B) (f : F), (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆) ∧
                row.ker = (centralizer (F : Set G)).subgroupOf B ∧
                (∀ (l : L) (b b' : B), (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
                  ∀ w : W, row b' (Multiplicative.ofAdd w) =
                    row b (Multiplicative.ofAdd (ψ l⁻¹ w))) ∧
                (⨆ b : B, (row b).range).map D.subtype = ⁅B,F⁆ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hdim
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ L
  have hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
  obtain ⟨hperfect,_,_,hLD,hFL,_,_,_,_⟩ :=
    ((h.decomposable_five_partner_two_three_perfect_lift_kernel
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hdim
  obtain ⟨_,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hMcK : Mc ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer dF.normalized hnD
  have hnB : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl b hb
    exact ⟨le_normalizer_iff.mp hMcK l (hLMc hl) b hb.1,
      L.mul_mem (L.mul_mem hl hb.2) (L.inv_mem hl)⟩
  have hBF : ⁅B,F⁆ ≤ D := (commutator_mono (show B ≤ K from inf_le_left) le_rfl).trans
    (commutator_commutatorPreimage_le Mc F D hnD)
  let heF : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let := heF
  let heD : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le dF.kernel_le
  let := heD
  exact ⟨hperfect,hnB,hLD,hFL,hBF,heD,
    exists_central_section_rows Mc F D L B ρ dF hLMc (inf_le_right.trans hLD) hLD hBF⟩

/-- The same literal rows for the section kernel inside the normal closure
of the original module. This retains the original actors before passing
to the canonical perfect lift. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_normal_kernel_rows
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
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let B := K ⊓ N.map Mc.subtype
          let hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
          let ψ := ρ.comp (Subgroup.inclusion hLMc)
          Group.IsPerfect L ∧ L ≤ normalizer (B : Set G) ∧
            L ≤ centralizer (D : Set G) ∧ L ≤ N.map Mc.subtype ∧
            N.map Mc.subtype ≤ centralizer (D : Set G) ∧ ⁅F,L⁆ = F ∧ ⁅B,F⁆ ≤ D ∧
            ∃ heD : IsElementaryAbelian 2 D,
              letI := heD
              ∃ row : B →* (Multiplicative W →* D),
                (∀ (b : B) (f : F), (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆) ∧
                row.ker = (centralizer (F : Set G)).subgroupOf B ∧
                (∀ (l : L) (b b' : B), (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
                  ∀ w : W, row b' (Multiplicative.ofAdd w) =
                    row b (Multiplicative.ofAdd (ψ l⁻¹ w))) ∧
                (⨆ b : B, (row b).range).map D.subtype = ⁅B,F⁆ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hdim
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ N.map Mc.subtype
  have hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
  obtain ⟨hperfect,_,_,hLD,hFL,_,_,_,_⟩ :=
    ((h.decomposable_five_partner_two_three_perfect_lift_kernel
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hdim
  obtain ⟨_,_,hDC,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hUE := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le (hUE.trans inf_le_left))).trans (localModule_centralizer_le_partner T Mc hu)
  have hNmap : N.map Mc.subtype = conjugateSpanBy V Mc := by
    rw [map_normalClosure_eq_conjugateSpanBy_range,
      map_subgroupOf_eq_of_le hVMc,range_subtype]
  have hND : N.map Mc.subtype ≤ centralizer (D : Set G) := by
    rw [hNmap]
    exact conjugateSpanBy_le (le_centralizer_iff.mp hDC)
      (hnD.trans (normalizer_le_normalizer_centralizer D))
  have hLN : L ≤ N.map Mc.subtype := map_mono (map_subtype_le (solvableResidual N))
  have hMcK : Mc ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer dF.normalized hnD
  have hMcN : Mc ≤ normalizer (N.map Mc.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro m hm _ ⟨n,hn,rfl⟩
    exact mem_map_of_mem Mc.subtype ((inferInstance : N.Normal).conj_mem n hn ⟨m,hm⟩)
  have hnB : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl b hb
    exact ⟨le_normalizer_iff.mp hMcK l (hLMc hl) b hb.1,
      le_normalizer_iff.mp hMcN l (hLMc hl) b hb.2⟩
  have hBF : ⁅B,F⁆ ≤ D := (commutator_mono (show B ≤ K from inf_le_left) le_rfl).trans
    (commutator_commutatorPreimage_le Mc F D hnD)
  let heF : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let := heF
  let heD : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le dF.kernel_le
  let := heD
  exact ⟨hperfect,hnB,hLD,hLN,hND,hFL,hBF,heD,
    exists_central_section_rows Mc F D L B ρ dF hLMc (inf_le_right.trans hND) hLD hBF⟩

end CFSG.Quasithin.Chapter15.Section01
