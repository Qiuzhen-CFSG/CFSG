module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryLocalResidual
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualCentralizer
public import Theory.Representation.G2BinarySylowFixedSpace
public import Theory.Representation.G2BinaryParabolicFrame
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.PResidual.CentralModuleFixed
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# Residual fixers in an intrinsic G₂(2) block

Align the component Sylow subgroup in the original two-core quotient with
its concrete G₂(2)′ model. The point parabolic fixes every Sylow-fixed
natural vector. Removing the central error by the two-residual comparison
places its three-residual inside the actual centralizer residual in L.
The concrete parabolic fixer theorem then makes every Sylow-preserving
automorphism fixing that residual trivial on L/O₂(L).

For a Sylow-normalized block K, the kernel of the literal KT action on
K/O₂(K) is a two-group: its intersection with K is O₂(K), and KT/K is
a two-group. Hence trivial quotient action places an element in O₂(KT).
The Chapter 12 G₂ core application uses both statements on the original
local centralizer; no split extension is assumed.

Source: Aschbacher–Smith 3.3.27(3), printed p.600, and B.4.6. The concrete
G₂ calculations reuse the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.G2BlockAction
open Atlas.G2 Atlas.G2.BinaryParabolicPair
abbrev Actor := commutator (Atlas.G2.Model (ZMod 2))
abbrev Vector := Atlas.G2.Natural.Space (ZMod 2)
variable {L : Type*} [Group L] [Finite L]

private def conjugated (m : BlockModuleModel L g2TwoNaturalAction) (g : Actor) :
    BlockModuleModel L g2TwoNaturalAction where
  quotientIso := m.quotientIso.trans (MulAut.conj g)
  moduleIso := m.moduleIso.trans (g2TwoNaturalAction g)
  intertwining l u := by
    change g2TwoNaturalAction g (m.moduleIso _) =
      g2TwoNaturalAction (g * m.quotientIso _ * g⁻¹)
        (g2TwoNaturalAction g (m.moduleIso _))
    rw [m.intertwining]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]

theorem exists_aligned_model (m : BlockModuleModel L g2TwoNaturalAction) (S : Sylow 2 L) :
    ∃ m' : BlockModuleModel L g2TwoNaturalAction,
      (S : Subgroup L).map m'.actor = (derivedSylow : Subgroup Actor) := by
  let P : Sylow 2 (commutator (Atlas.G2.Model (ZMod 2))) :=
    S.mapSurjective (f := m.actor) m.actor_surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (commutator (Atlas.G2.Model (ZMod 2))) P derivedSylow
  refine ⟨conjugated m g, ?_⟩
  have he : (conjugated m g).actor = (MulAut.conj g).toMonoidHom.comp m.actor := rfl
  rw [he, ← map_map]
  exact congrArg (fun P : Sylow 2 Actor => (P : Subgroup Actor)) hg

@[expose] def modulePoint (m : BlockModuleModel L g2TwoNaturalAction)
    (u : blockU L) : Vector := (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd

omit [Finite L] in
private theorem central_error_iff (m : BlockModuleModel L g2TwoNaturalAction)
    (l : L) (u : blockU L) :
    ⁅l, (u : L)⁆ ∈ center L ↔
      Natural.derivedAction (ZMod 2) (m.actor l) (modulePoint m u) = modulePoint m u := by
  change blockConjugate L l u * u⁻¹ ∈ blockFixed L ↔ _
  rw [← QuotientGroup.eq_one_iff, ← m.moduleIso.map_eq_one_iff]
  change m.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u * u⁻¹)) = 1 ↔ _
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one, m.intertwining]
  exact Multiplicative.toAdd.injective.eq_iff.symm

private theorem point_parabolic_fixes_sylow_fixed (v : Vector)
    (hv : v ∈ Representation.BinaryOffender.fixedSpace
      (Natural.derivedAction (ZMod 2)) (derivedSylow : Subgroup Actor))
    (g : Actor) (hg : g ∈ derivedSecond) :
    Natural.derivedAction (ZMod 2) g v = v := by
  let e := Restricted.NaturalCoordinates.equiv (ZMod 2)
  have he (w : Vector) : e w = Natural.binaryCoordinates (ZMod 2) w := by
    obtain ⟨x,rfl⟩ := Natural.mk_surjective (ZMod 2) w
    rfl
  apply e.injective
  change e (Natural.action (ZMod 2) g.val v) = e v
  rw [show e (Natural.action (ZMod 2) g.val v) =
    Restricted.NaturalCoordinates.action (ZMod 2) g.val (e v) from
      LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining' g.val) v]
  apply Natural.BinaryPointFlag.pointParabolic_fixes_pointLine g.val hg
  rw [Natural.BinaryPointFlag.mem_pointLine]
  intro i hi
  rw [he, Natural.BinarySylowFixedSpace.derivedSylow_fixed_coordinates v hv]
  fin_cases i <;> simp_all

/-- The parabolic three-residual lies in the actual residual centralizer
of every subgroup of U fixed by the marked component Sylow. -/
theorem secondResidual_le_centralizer_image
    (m : BlockModuleModel L g2TwoNaturalAction) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map m.actor = (derivedSylow : Subgroup Actor))
    (E : Subgroup L) (hEU : E ≤ blockU L) (hES : E ≤ centralizer (S : Set L)) :
    secondResidual ≤ (pResidual 2 (centralizer (E : Set L))).map
      ((m.actor).comp (centralizer (E : Set L)).subtype) := by
  let B := commutatorPreimage (⊤ : Subgroup L) E (center L)
  have hPB : derivedSecond ≤ B.map m.actor := by
    intro a ha
    obtain ⟨l,rfl⟩ := m.actor_surjective a
    refine ⟨l, ?_, rfl⟩
    apply (mem_commutatorPreimage_iff ⊤ E (center L) le_normalizer_of_normal l).mpr
    refine ⟨mem_top _, ?_⟩
    intro u hu
    let uU : blockU L := ⟨u,hEU hu⟩
    apply (central_error_iff m l uU).mpr
    apply point_parabolic_fixes_sylow_fixed _ ?_ _ ha
    rintro ⟨a,haS⟩
    rw [← hS] at haS
    obtain ⟨s,hs,rfl⟩ := haS
    have hh := m.g2_intertwining s uU
    have he : blockConjugate L s uU = uU := by
      apply Subtype.ext
      change s * u * s⁻¹ = u
      rw [hES hu s hs, mul_inv_cancel_right]
    rw [he] at hh
    exact hh.symm
  have hr := embedded_pResidual_mono 2 hPB
  have hc := embedded_residual_centralizer_eq_central_preimage
    (blockU L) E (center L) (pCore_isPGroup.to_le blockU_le_core) hEU le_rfl
  rw [← map_map, hc, map_embedded_pResidual]
  exact (map_mono (f := derivedSecond.subtype) primeToResidual_three_le_twoResidual).trans hr

/-- A Sylow-preserving block automorphism fixing the literal centralizer
residual has trivial action on the original two-core quotient. -/
theorem quotientAction_eq_one_of_centralizer_residual
    (m : BlockModuleModel L g2TwoNaturalAction) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map m.actor = (derivedSylow : Subgroup Actor))
    (E : Subgroup L) (hEU : E ≤ blockU L) (hES : E ≤ centralizer (S : Set L))
    (a : MulAut L) (haS : (S : Subgroup L).map a.toMonoidHom = S)
    (haC : ∀ x ∈ (pResidual 2 (centralizer (E : Set L))).map
      (centralizer (E : Set L)).subtype, a x = x) : m.quotientAction a = 1 := by
  apply automorphism_eq_one_of_secondResidual
  · rw [← hS, map_map]
    have he : (m.quotientAction a).toMonoidHom.comp m.actor =
        m.actor.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro l
      exact m.quotientAction_actor a l
    rw [he, ← map_map, haS]
  · intro x hx
    have hm := secondResidual_le_centralizer_image m S hS E hEU hES hx
    rw [← map_map] at hm
    obtain ⟨l,hl,rfl⟩ := hm
    rw [m.quotientAction_actor, haC l hl]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K : Subgroup G}

/-- Conjugation by KT, on the actual core quotient of the G₂ block. -/
@[expose] def joinAction (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    ↥(K ⊔ (T : Subgroup G)) →* MulAut Actor :=
  m.quotientAction.comp (K.normalizerMonoidHom.comp
    (inclusion (sup_le K.le_normalizer hTK)))

omit [Finite G] in
/-- The kernel is a two-group: on K it is exactly O₂(K), and KT/K is a two-group. -/
theorem joinAction_kernel_isPGroup
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    IsPGroup 2 (joinAction hTK m).ker := by
  let H := K ⊔ (T : Subgroup G)
  let K₀ := K.subgroupOf H
  let P := (T : Subgroup G).subgroupOf H
  let q := joinAction hTK m
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  apply q.kernel_isPGroup_of_normal_supplement K₀ P T.isPGroup'.comap_subtype
    (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  let e : K₀ ≃* K := subgroupOfEquivOfLe le_sup_left
  let f := q.comp K₀.subtype
  have hf (x : f.ker) : e x.val ∈ pCore 2 K := by
    have hc : m.actor (e x.val) ∈ center Actor := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨k,rfl⟩ := m.actor_surjective y
      have hh := congrArg (fun b : MulAut Actor => b (m.actor k)) x.property
      change m.quotientAction (K.normalizerMonoidHom
        (inclusion (sup_le K.le_normalizer hTK) x.val.val)) (m.actor k) = m.actor k at hh
      rw [m.quotientAction_actor] at hh
      change m.actor (e x.val * k * (e x.val)⁻¹) = m.actor k at hh
      rw [map_mul, map_mul, map_inv] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have he : m.actor (e x.val) = 1 := by
      simpa only [BinaryLocalResidual.center_eq_bot,mem_bot] using hc
    exact (QuotientGroup.eq_one_iff (e x.val)).mp
      (m.quotientIso.map_eq_one_iff.mp he)
  let r : f.ker →* pCore 2 K := (e.toMonoidHom.comp f.ker.subtype).codRestrict _ hf
  apply (pCore_isPGroup (p := 2) (G := K)).of_injective r
  intro x y hxy
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val hxy)

omit [Finite G] in
/-- Trivial quotient action puts the original element in the actual local two-core. -/
theorem mem_core_of_joinAction_eq_one
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (x : ↥(K ⊔ (T : Subgroup G))) (hx : joinAction hTK m x = 1) :
    (x : G) ∈ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hk : (joinAction hTK m).ker ≤ pCore 2 ↥(K ⊔ (T : Subgroup G)) :=
    le_sSup ⟨inferInstance, joinAction_kernel_isPGroup hTK m⟩
  exact mem_map_of_mem (K ⊔ (T : Subgroup G)).subtype (hk hx)
end CFSG.Quasithin.ChapterC.G2BlockAction
