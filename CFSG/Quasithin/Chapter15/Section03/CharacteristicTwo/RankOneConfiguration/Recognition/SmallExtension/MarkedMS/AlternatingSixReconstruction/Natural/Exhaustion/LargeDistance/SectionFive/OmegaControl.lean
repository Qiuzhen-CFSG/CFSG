module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaExtension
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaExtension
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed

/-!
# Full omega control in the permutation-extension case

A singleton displacement witness supplies a complement to each
transposition's fixed hyperplane. The line centralizer moves that complement
only within the critical line. The core map can kill the constant vector:
the proof only uses that its kernel is contained in the natural quotient's
kernel, so both moved-cover orders sixteen and thirty-two remain possible.

For the literal omega action, this gives
`[Y,X] <= [X,A] join [Y,C_X(A)]` whenever Y fixes the critical line and A
has the original transposition image. Transport through the actual graph
embedding identifies C_X(A) with X intersect Q at the opposite endpoint.
Thus full X is centrally generated, or this displacement control holds.
For a span normalized by the full kernel, the second alternative makes its
join with the opposite seed invariant under X.

The original shifted application retains the same component conjugator,
every shared path vertex, and the complete seed-kernel line data. Either
its literal R_3 is that order-two central line, or the whole shifted local
stabilizer normalizes D join Z_c. This discharges the permutation-extension
calculation behind MS93 (3.3)(ii); excluding that actual normalization
alternative is still needed for the unconditional R_3 identity and strict
slice. The span comparison and terminal distance exclusions remain open.

The private coordinate and graph helpers from FullSeed, FullKernel and
OmegaExtension are used as an intentional internal proof continuation.
Their public interfaces and exposed bodies are unchanged.
Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), printed pp.866--867,
and its full-X application in (5.9), printed pp.920--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SeedCoordinates
variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]

private theorem core_kernel_le_natural
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (pairVector i k) ≠ 0) :
    j.toLinearMap.ker ≤ (coreToNatural (Fin 6)).ker := by
  intro v hv
  have hsame (i k : Fin 6) : v.val i = v.val k := by
    by_cases he : i = k
    · exact congrArg v.val he
    have hd : j (displacement (Equiv.swap i k) v.val) = 0 := by
      change j (coreRepresentation (Fin 6) (Equiv.swap i k) v-v) = 0
      rw [map_sub,j.isIntertwining,show j v = 0 from hv,map_zero,sub_zero]
    rw [displacement_swap,map_smul] at hd
    have hz : v.val i + v.val k = 0 := (smul_eq_zero.mp hd).resolve_right (hj i k he)
    simpa only [CharTwo.add_eq_zero] using hz
  change coreToNatural (Fin 6) v = 0
  rw [←Subtype.val_inj]
  apply (Submodule.Quotient.mk_eq_zero (constants (Fin 6))).mpr
  exact (mem_constants_iff v.val).mpr ⟨v.val 0,fun i => hsame i 0⟩

private theorem fixed_pair_letters
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (pairVector i k) ≠ 0)
    (g : S) (i k : Fin 6) (hik : i ≠ k)
    (hg : ρ g (j (pairVector i k)) = j (pairVector i k)) :
    g i = i ∨ g i = k := by
  have he : coreToNatural (Fin 6) (coreRepresentation (Fin 6) g (pairVector i k)) =
      coreToNatural (Fin 6) (pairVector i k) := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    apply core_kernel_le_natural ρ j hj
    change j (coreRepresentation (Fin 6) g (pairVector i k)-pairVector i k) = 0
    rw [map_sub,j.isIntertwining,hg,sub_self]
  rw [coreToNatural_equivariant] at he
  change naturalRepresentation (Fin 6) g (NaturalGeometry.pairVector i k) =
    NaturalGeometry.pairVector i k at he
  rw [NaturalGeometry.pairVector_map] at he
  have hpair := (NaturalGeometry.pairVector_eq_iff (g.injective.ne hik) hik).mp he
  have hm : g i ∈ ({g i,g k} : Finset (Fin 6)) := by simp
  change ({g i,g k} : Finset (Fin 6)) = {i,k} at hpair
  rw [hpair] at hm
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hm

private theorem singleton_displacement (g : S) (i : Fin 6) :
    displacement g (Pi.single i 1) = pairVector (g i) i := by
  apply Subtype.ext
  ext k
  simp only [displacement,pairVector,representation_apply,Pi.sub_apply,Pi.add_apply,
    CharTwo.sub_eq_add]
  congr 1
  simp only [Pi.single_apply]
  congr 1
  exact propext (Equiv.symm_apply_eq g)

/-- A singleton-coordinate omega vector supplies a complement to each
transposition's fixed hyperplane. Its displacement under the critical-line
centralizer stays in that line, with no splitting of the moved cover. -/
theorem singleton_fixed_complement
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (pairVector i k) ≠ 0)
    (x : Y) (hx : ∀ g : S, ρ g x-x = j (displacement g (Pi.single 0 1)))
    (i k : Fin 6) (hik : i ≠ k) :
    ∃ c : Y, ρ (Equiv.swap i k) c-c = j (pairVector i k) ∧
      ∀ g : S, ρ g (j (pairVector i k)) = j (pairVector i k) →
        ρ g c-c = 0 ∨ ρ g c-c = j (pairVector i k) := by
  let c := x-j (pairVector 0 i)
  have hc (g : S) : ρ g c-c = j (displacement g (Pi.single i 1)) := by
    have hword : (Pi.single 0 1 : Full (Fin 6))-(pairVector 0 i).val = Pi.single i 1 := by
      change Pi.single 0 1-(Pi.single 0 1+Pi.single i 1) = Pi.single i 1
      ext a
      simp only [Pi.sub_apply,Pi.add_apply,CharTwo.sub_eq_add]
      rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]
    have hd : displacement g (Pi.single 0 1)-
        (coreRepresentation (Fin 6) g (pairVector 0 i)-pairVector 0 i) =
        displacement g (Pi.single i 1) := by
      apply Subtype.ext
      change (representation (Fin 6) g (Pi.single 0 1)-Pi.single 0 1)-
        (representation (Fin 6) g (pairVector 0 i).val-(pairVector 0 i).val) = _
      rw [show (representation (Fin 6) g (Pi.single 0 1)-Pi.single 0 1)-
        (representation (Fin 6) g (pairVector 0 i).val-(pairVector 0 i).val) =
        representation (Fin 6) g (Pi.single 0 1-(pairVector 0 i).val)-
          (Pi.single 0 1-(pairVector 0 i).val) by rw [map_sub]; abel,hword]
      rfl
    dsimp only [c]
    rw [map_sub]
    calc
      _ = (ρ g x-x)-(ρ g (j (pairVector 0 i))-j (pairVector 0 i)) := by abel
      _ = j (displacement g (Pi.single 0 1))-
          j (coreRepresentation (Fin 6) g (pairVector 0 i)-pairVector 0 i) := by
        rw [hx,map_sub,j.isIntertwining]
      _ = _ := by rw [←map_sub,hd]
  refine ⟨c,?_,?_⟩
  · rw [hc,singleton_displacement,Equiv.swap_apply_left]
    congr 1
    apply Subtype.ext
    exact add_comm _ _
  · intro g hg
    rw [hc,singleton_displacement]
    rcases fixed_pair_letters ρ j hj g i k hik hg with he | he
    · left
      rw [he,show pairVector i i = 0 by apply Subtype.ext; ext a; exact CharTwo.add_self_eq_zero _,map_zero]
    · right
      rw [he]
      congr 1
      apply Subtype.ext
      exact add_comm _ _

/-- In the permutation-extension case, fixing the critical line controls
all displacement modulo the displacement of the full fixed hyperplane. -/
theorem singleton_displacement_control [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (pairVector i k) ≠ 0)
    (x : Y) (hx : ∀ g : S, ρ g x-x = j (displacement g (Pi.single 0 1)))
    (i k : Fin 6) (hik : i ≠ k)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ (Equiv.swap i k)-LinearMap.id)) = 1)
    (g : S) (hg : ρ g (j (pairVector i k)) = j (pairVector i k))
    (N : Submodule (ZMod 2) Y) (hN : j (pairVector i k) ∈ N)
    (hfixed : ∀ v : Y, ρ (Equiv.swap i k) v = v → ρ g v-v ∈ N) :
    ∀ v : Y, ρ g v-v ∈ N := by
  obtain ⟨c,hc,hgc⟩ := singleton_fixed_complement ρ j hj x hx i k hik
  let D := ρ (Equiv.swap i k)-LinearMap.id
  have he : Submodule.span (ZMod 2) {j (pairVector i k)} = D.range := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact ⟨c,hc⟩
    · rw [finrank_span_singleton (hj i k hik)]
      exact hr.le
  intro v
  have hd : D v ∈ Submodule.span (ZMod 2) {j (pairVector i k)} :=
    he.symm ▸ LinearMap.mem_range_self D v
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hd
  have hv : ρ (Equiv.swap i k) (v-a • c) = v-a • c := by
    apply sub_eq_zero.mp
    rw [map_sub,map_smul]
    calc
      _ = (ρ (Equiv.swap i k) v-v)-a • (ρ (Equiv.swap i k) c-c) := by rw [smul_sub]; abel
      _ = 0 := by rw [hc,ha]; exact sub_self _
  have hw := hfixed (v-a • c) hv
  have hcg : ρ g c-c ∈ N := by
    rcases hgc g hg with he | he
    · rw [he]; exact N.zero_mem
    · rwa [he]
  have hh := N.add_mem hw (N.smul_mem a hcg)
  convert hh using 1
  rw [map_sub,map_smul,smul_sub]
  abel
end SeedCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "X₀" => omegaCenterIn (pCore 2 d.overgroup)
variable [hOmega : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup))]

private theorem omega_displacement_value (g : d.overgroup) (v : Additive X₀) :
    ((omegaAction s (s.projection g) v-v).toMul : d.overgroup) = ⁅g,(v.toMul : d.overgroup)⁆ := by
  rw [toMul_sub,div_eq_mul_inv]
  change ((omegaAction s (s.projection g) v).toMul : d.overgroup) * (v.toMul : d.overgroup)⁻¹ = _
  rw [omegaAction_conjugate]
  rfl

/-- Literal full-omega displacement control, with the original projection and
with the entire fixed kernel retained. -/
theorem omega_singleton_commutator_control
    (j : (coreRepresentation (Fin 6)).IntertwiningMap (omegaAction s))
    (hj : ∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0)
    (x : Additive X₀)
    (hx : ∀ g : Equiv.Perm (Fin 6), omegaAction s g x-x =
      j (SeedCoordinates.displacement g (Pi.single 0 1)))
    (A : Subgroup d.overgroup) (i k : Fin 6) (hik : i ≠ k)
    (hA : A.map s.projection = zpowers (Equiv.swap i k))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (omegaAction s (Equiv.swap i k)-LinearMap.id)) = 1)
    (Y : Subgroup d.overgroup)
    (hY : Y ≤ centralizer ((⁅X₀,A⁆ : Subgroup d.overgroup) : Set d.overgroup)) :
    ⁅Y,X₀⁆ ≤ ⁅X₀,A⁆ ⊔ ⁅Y,X₀ ⊓ centralizer (A : Set d.overgroup)⁆ := by
  let N := ⁅X₀,A⁆ ⊔ ⁅Y,X₀ ⊓ centralizer (A : Set d.overgroup)⁆
  let W : Submodule (ZMod 2) (Additive X₀) :=
    AddSubgroup.toZModSubmodule 2 (N.subgroupOf X₀).toAddSubgroup
  let r := j (SeedCoordinates.pairVector i k)
  obtain ⟨c,hc,_⟩ := SeedCoordinates.singleton_fixed_complement (omegaAction s) j hj x hx i k hik
  obtain ⟨a,ha,hat⟩ := (show Equiv.swap i k ∈ A.map s.projection from hA.symm ▸ mem_zpowers _)
  have hrR : (r.toMul : d.overgroup) ∈ ⁅X₀,A⁆ := by
    have he := congrArg (fun v : Additive X₀ => (v.toMul : d.overgroup)) hc
    rw [←hat,omega_displacement_value] at he
    rw [←he,commutator_comm X₀ A]
    exact commutator_mem_commutator ha c.toMul.property
  apply commutator_le.mpr
  intro y hy v hv
  have hgr : omegaAction s (s.projection y) r = r := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [omegaAction_conjugate]
    exact mul_inv_eq_iff_eq_mul.mpr (hY hy _ hrR).symm
  have hNW : r ∈ W := (le_sup_left : ⁅X₀,A⁆ ≤ N) hrR
  have hfix (w : Additive X₀)
      (hw : omegaAction s (Equiv.swap i k) w = w) :
      omegaAction s (s.projection y) w-w ∈ W := by
    have hwa : (w.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup) := by
      intro a ha
      have hmem : s.projection a ∈ zpowers (Equiv.swap i k) := hA ▸ mem_map_of_mem _ ha
      have hh := ((mem_fixedSpace_zpowers_iff (omegaAction s) (Equiv.swap i k) w).mpr hw)
        ⟨s.projection a,hmem⟩
      change omegaAction s (s.projection a) w = w at hh
      have he := congrArg (fun v : Additive X₀ => (v.toMul : d.overgroup)) hh
      rw [omegaAction_conjugate] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    change ((omegaAction s (s.projection y) w-w).toMul : d.overgroup) ∈ N
    rw [omega_displacement_value]
    exact (le_sup_right : ⁅Y,X₀ ⊓ centralizer (A : Set d.overgroup)⁆ ≤ N)
      (commutator_mem_commutator hy ⟨w.toMul.property,hwa⟩)
  have hh := SeedCoordinates.singleton_displacement_control (omegaAction s) j hj x hx i k hik hr
    (s.projection y) hgr W hNW hfix (Additive.ofMul (⟨v,hv⟩ : X₀))
  change ((omegaAction s (s.projection y) (Additive.ofMul (⟨v,hv⟩ : X₀))-
    Additive.ofMul (⟨v,hv⟩ : X₀)).toMul : d.overgroup) ∈ N at hh
  rwa [omega_displacement_value] at hh

include s in
/-- The original omega layer is centrally generated, or every local actor
fixing the critical line satisfies the full-kernel displacement bound. -/
theorem full_X_generation_or_control (hc : DistanceTwo.CentralLayer d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4) :
    X d.radical (alpha d.radical) = U d.radical (alpha d.radical) ⊔
      (X d.radical (alpha d.radical) ⊓ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) ∨
    ∀ Y : Subgroup (FreeAmalgam d.radical), Y ≤ stabilizer d.radical (alpha d.radical) →
      Y ≤ centralizer ((⁅X d.radical (alpha d.radical),Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) →
      ⁅Y,X d.radical (alpha d.radical)⁆ ≤ ⁅X d.radical (alpha d.radical),Z d.radical z⁆ ⊔
        ⁅Y,X d.radical (alpha d.radical) ⊓ Q d.radical z⁆ := by
  rcases full_X_generation_or_singleton s hc p hsmall with hgen | ⟨j,_,hj,x,hx⟩
  · exact Or.inl hgen
  right
  intro Y hYG hYR
  let A := (Z d.radical z).comap (embedM d.radical)
  let Y₀ := Y.comap (embedM d.radical)
  have hAm : A.map (embedM d.radical) = Z d.radical z := map_comap_eq_self
    (((seed_le_full_X (h := h) p.end_color).trans (critical_full_X_local s hc p).2).trans_eq (stabilizer_m_base d.radical))
  have hYm : Y₀.map (embedM d.radical) = Y :=
    map_comap_eq_self (hYG.trans_eq (stabilizer_m_base d.radical))
  have hRm : (⁅X₀,A⁆ : Subgroup d.overgroup).map (embedM d.radical) =
      ⁅X d.radical (alpha d.radical),Z d.radical z⁆ := by
    rw [map_commutator,omega_map (h := h),hAm]
  have hY₀ : Y₀ ≤ centralizer ((⁅X₀,A⁆ : Subgroup d.overgroup) : Set d.overgroup) := by
    intro y hy r hr
    apply embedM_injective d.radical
    simpa only [map_mul] using hYR hy (embedM d.radical r)
      (hRm ▸ mem_map_of_mem (embedM d.radical) hr)
  obtain ⟨t,⟨i,k,hik,rfl⟩,ht⟩ := small_critical_image_eq_swap
    (κ := KnownSimple.IsKnownSimple) (h := h) (d := d) s hc p hsmall
  have hbound := omega_singleton_commutator_control s j hj x hx A i k hik ht
    (omega_transposition_rank_one s hc p hsmall i k hik) Y₀ hY₀
  have hK : X d.radical (alpha d.radical) ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) =
      X d.radical (alpha d.radical) ⊓ Q d.radical z := by
    apply le_antisymm
    · intro v hv
      refine ⟨hv.1,?_⟩
      rw [←C_eq_Q s hc z p.end_color]
      exact ⟨(critical_full_X_local s hc p).1 hv.1,hv.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        ((seed_le_full_X (h := h) p.end_color).trans
          (le_centralizer_iff.mp (Q_le_centralizer_X d.radical z))))
  have hm := map_mono (f := embedM d.radical) hbound
  rw [Subgroup.map_sup,map_commutator,hYm,omega_map (h := h),hRm,map_commutator,hYm,
    ←map_inf_centralizer_of_injective _ (embedM_injective d.radical),
    omega_map (h := h),hAm,hK] at hm
  exact hm

include s in
/-- The full-kernel alternative at every actual vertex, transported through
free-amalgam conjugation rather than a new action marking. -/
theorem full_X_generation_or_control_at (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∨
    ∀ Y : Subgroup (FreeAmalgam d.radical), Y ≤ stabilizer d.radical a →
      Y ≤ centralizer ((⁅X d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) →
      ⁅Y,X d.radical a⁆ ≤ ⁅X d.radical a,Z d.radical z⁆ ⊔ ⁅Y,X d.radical a ⊓ Q d.radical z⁆ := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  subst a
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hi : Function.Injective f := (MulAut.conj (g⁻¹)⁻¹).injective
  have hh := full_X_generation_or_control s hc (z := act d.radical g⁻¹ z)
  rw [←hbase] at hh
  have hs : (Q d.radical (act d.radical g⁻¹ z)).relIndex
      (Z d.radical (act d.radical g⁻¹ (mVertex d.radical g))) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ hi]
    exact hsmall
  rcases hh (p.act g⁻¹) hs with hgen | hcontrol
  · left
    apply map_injective hi
    rw [Subgroup.map_sup,←map_inf_centralizer_of_injective _ hi]
    simpa only [X_act,U_act,stabilizer_act] using hgen
  · right
    intro Y hYG hYR
    have hYG' : Y.map f ≤ stabilizer d.radical (act d.radical g⁻¹ (mVertex d.radical g)) := by
      rw [stabilizer_act]
      exact map_mono hYG
    have hYR' : Y.map f ≤ centralizer
        ((⁅X d.radical (act d.radical g⁻¹ (mVertex d.radical g)),Z d.radical (act d.radical g⁻¹ z)⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [X_act,Z_act,←map_commutator,←map_commutator,
        commutator_eq_bot_iff_le_centralizer.mpr hYR,Subgroup.map_bot]
    have hb := hcontrol (Y.map f) hYG' hYR'
    rw [X_act,Z_act,Q_act,←map_commutator,←map_commutator,
      ←Subgroup.map_inf _ _ f hi,←map_commutator,←Subgroup.map_sup] at hb
    exact (map_le_map_iff_of_injective hi).mp hb

include s in
/-- In the extension case, a span normalized by the full critical kernel
has a normalized join with the opposite seed. This is the literal
normalization alternative needed before applying source nonnormality. -/
theorem critical_X_generation_or_normalization (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (D : Subgroup (FreeAmalgam d.radical)) (hDz : D ≤ stabilizer d.radical z)
    (hDQ : D ≤ Q d.radical a)
    (hN : X d.radical z ⊓ Q d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical))) :
    X d.radical z = U d.radical z ⊔
      (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∨
    X d.radical z ≤ normalizer ((D ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let q : CriticalPath d.radical (replacementGeometry h d) z a :=
    CriticalPath.ofPair p.end_color (critical_reverse_pair s hc p)
  have hs : (Q d.radical a).relIndex (Z d.radical z) < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  rcases full_X_generation_or_control_at s hc q hs with hgen | hcontrol
  · exact Or.inl hgen
  right
  have hXN : X d.radical z ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (critical_full_X_local s hc p).2.trans (Z_normalized d.radical a)
  have hRZ : ⁅X d.radical z,Z d.radical a⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_right.mp hXN
  have hDR : D ≤ centralizer
      ((⁅X d.radical z,Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) :=
    (hDQ.trans (Q_le_centralizer_X d.radical a)).trans
      (centralizer_le (hRZ.trans (seed_le_full_X (h := h) p.start_color)))
  have hcom : ⁅X d.radical z,D⁆ ≤ D ⊔ Z d.radical a := by
    rw [commutator_comm]
    exact (hcontrol D hDz hDR).trans (sup_le (hRZ.trans le_sup_right)
      ((le_normalizer_iff_commutator_le_left.mp hN).trans le_sup_left))
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hm : (D ⊔ Z d.radical a).map (MulAut.conj x).toMonoidHom ≤ D ⊔ Z d.radical a := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
    rintro _ ⟨y,hy,rfl⟩
    have hh := (D ⊔ Z d.radical a).mul_mem
      (hcom (commutator_mem_commutator hx hy)) (mem_sup_left hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)

/-- The literal shifted R₃ is the proved central seed-kernel line, or its
whole shifted stabilizer normalizes the actual seed-span join. The same component
conjugator and every shared path vertex are retained in both alternatives.
Excluding the second alternative remains necessary for the strict slice. -/
theorem full_point_small_shifted_X_normalization_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ t, Adjacent d.radical c t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical c ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        let D := conjugateSpanBy (Z d.radical a) P
        let J := ⁅D,Z d.radical z ⊓ Q d.radical c⁆
        let A₀ := X d.radical z ⊓ Q d.radical c
        let R₃ := ⁅D,A₀⁆
        H₂ ≤ U d.radical c ⊓ Z d.radical t ∧
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        D ≤ Q d.radical a' ∧
        (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
        Nat.card J = 2 ∧ J ≤ Z d.radical z ∧
        J ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
        J ⊓ ⁅Z d.radical c,Z d.radical z⁆ = ⊥ ∧
        J ≤ fixedCore d.radical c ∧ J ≤ Z d.radical a ∧ J ≠ H₂ ∧
        (∃ x ∈ P, ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
          Z d.radical z ⊓ Q d.radical c⁆ = J) ∧
        Q d.radical c ⊔ X d.radical z = Q d.radical c ⊔ Z d.radical z ∧
        ⁅X d.radical c,X d.radical z⁆ = ⁅Z d.radical c,Z d.radical z⁆ ∧
        stabilizer d.radical z ⊓ centralizer (A₀ : Set (FreeAmalgam d.radical)) =
          Q d.radical z ⊔ Z d.radical c ∧
        J ≤ R₃ ∧ R₃ ≠ ⊥ ∧ R₃ ≤ D ⊓ A₀ ∧
        (R₃ = J ∨ stabilizer d.radical c ≤ normalizer
          ((D ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hDQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,hxJ,hjoin,hcom,hfix,hJR,hRne,hRA,_⟩ :=
    full_point_small_shifted_X_kernel_knownSimple hb u hfull p hslice hsmall
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let J := ⁅D,Z d.radical z ⊓ Q d.radical c⁆
  let A₀ := X d.radical z ⊓ Q d.radical c
  let R₃ := ⁅D,A₀⁆
  have hDZ : D ≤ stabilizer d.radical z :=
    hDQ.trans (Q_le_stabilizer_of_dist_two d.radical a' z p.end_color haz)
  have hZaV : Z d.radical a ≤ V d.radical c := by
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hZV : Z d.radical (alpha d.radical) ≤ V d.radical c :=
      le_iSup_of_le (alpha d.radical) (le_iSup_of_le
        (show (cosetGraph d.radical).dist (alpha d.radical) c ≤ 2 from
          (p.dist_start (by omega)).le) le_rfl)
    change Z d.radical (act d.radical y⁻¹ (alpha d.radical)) ≤ V d.radical c
    rw [Z_act,inv_inv]
    exact (map_mono hZV).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized d.radical c (Ltilde_le_stabilizer c hy)))
  have hDV : D ≤ V d.radical c :=
    conjugateSpanBy_le hZaV (inf_le_left.trans (V_normalized c))
  have hDc : D ≤ Q d.radical c :=
    hDV.trans ((replacementGeometry h d).V_le_Q
      (show 2 < replacementDistance h d by omega) c q.start_color)
  have hQcP : Q d.radical c ≤ P :=
    le_inf (fun _ hx => hx.1)
      ((Q_le_centralizer_X d.radical c).trans
        (centralizer_le ((hHseed.trans inf_le_left).trans
          ((DistanceEight.U_le_Z d.radical c).trans (seed_le_full_X (h := h) q.start_color)))))
  have hN : A₀ ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans hQcP).trans (le_normalizer_conjugateSpanBy _ _)
  have hsmall' : (Q d.radical z).relIndex (Z d.radical c) < 4 := by
    rw [hidx]
    decide
  refine ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hDQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,hxJ,hjoin,hcom,hfix,hJR,hRne,hRA,?_⟩
  rcases critical_X_generation_or_normalization s hc q hsmall' D hDZ hDc hN with hgen | hnorm
  · exact Or.inl (critical_X_kernel_commutator_of_central_generation s hc q hgen D hDZ hN)
  · right
    refine hPgen.ge.trans (sup_le ?_ ?_)
    · exact (le_inf (le_normalizer_conjugateSpanBy (Z d.radical a) P)
        (inf_le_left.trans (Z_normalized d.radical c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (seed_le_full_X (h := h) q.end_color).trans hnorm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
