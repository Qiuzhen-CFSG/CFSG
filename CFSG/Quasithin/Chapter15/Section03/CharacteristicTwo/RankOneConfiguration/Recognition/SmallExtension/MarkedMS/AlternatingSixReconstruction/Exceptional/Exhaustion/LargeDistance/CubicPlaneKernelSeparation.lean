module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels

/-!
# Distinct midpoint kernels on the same selected cubic span

At distance four, suppose the two literal end slices of an original plane
critical path have index at most two. Put P equal to the selected seed span
and Y = P intersect Q_c at its midpoint c. The paired selector gives a
switch x normalizing the first-edge Thompson join. The preceding endpoint
control holds for Y at the original endpoint but fails for Y at the switched
endpoint. Conjugating the original estimate supplies it there for
Y' = P intersect Q_(c^x), since x normalizes P.

Thus Y is not contained in Y'. Both have index two in P, so they generate P
and have intersection of index four. The same switch does not normalize Y.
Both kernels retain the entire derived line of P, of order two. The proof
also transports the full reverse-kernel centralization and retains every
path vertex, the original component lift and both generation identities.

This is the literal kernel-separation calculation needed in the comparison
on MS93 p.927. The two end-slice bounds remain explicit; their source proof
requires the earlier shifted-path normality and generation argument. This
result does not supply those bounds or identify the two midpoint cores.
The whole-core and C.1.32 consumers retain the Borel branch, both covers,
the original projection kernel E and its nontrivial odd quotient E/Q.
Larger-distance exclusions and both final core exhaustions remain open.

The internal import reuses the existing finite index-two intersection lemma
without changing its public boundary.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(3), printed pp.926--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The same selected switch separates the two literal midpoint kernels
inside the original span. Both retain its full derived line. -/
theorem plane_four_selected_kernel_separation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    let c := p.walk.getVert 2
    let P := localZSpan Rg c (alpha Rg)
    let Y := P ⊓ Q Rg c
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      let Y' := P ⊓ Q Rg (act Rg x c)
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) =
          stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
          stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
          Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        Y.map (MulAut.conj x⁻¹).toMonoidHom = Y' ∧
        x ∉ normalizer (Y : Set (FreeAmalgam Rg)) ∧
        ¬ Y ≤ Y' ∧ ¬ Y' ≤ Y ∧ Y ⊔ Y' = P ∧
        Y.relIndex P = 2 ∧ Y'.relIndex P = 2 ∧ (Y ⊓ Y').relIndex P = 4 ∧
        ⁅Y,Y⁆ = ⁅P,P⁆ ∧ ⁅Y',Y'⁆ = ⁅P,P⁆ ∧
        Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
        ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧
        ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
        ⁅Y',Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧
        ⁅Y',Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) ∧
        ¬ ⁅Y,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨hzero,hcontrol,t,hat,r,hr,q,hq,hgen,hpair,hnorm,hinside,hbad⟩ :=
    plane_four_selected_pair_of_slices h e hz hk u hR hb4 p hforward hopposite
  let c := p.walk.getVert 2
  let P := localZSpan Rg c (alpha Rg)
  let Y := P ⊓ Q Rg c
  let x := (embedM Rg r)⁻¹
  let Y' := P ⊓ Q Rg (act Rg x c)
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hPm : P.map (MulAut.conj x⁻¹).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg c (alpha Rg) ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hZm : (Z Rg (alpha Rg)).map (MulAut.conj x⁻¹).toMonoidHom =
      Z Rg (alpha Rg) := mem_normalizer_iff_map_conj_eq.mp
    (Z_normalized Rg _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hQm : (Q Rg (alpha Rg)).map (MulAut.conj x⁻¹).toMonoidHom =
      Q Rg (alpha Rg) := mem_normalizer_iff_map_conj_eq.mp
    (Q_normalized Rg _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hYm : Y.map (MulAut.conj x⁻¹).toMonoidHom = Y' := by
    dsimp only [Y,Y']
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,hPm,←Q_act]
  have hcontrol' : ⁅Y',Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hcontrol
    rw [map_commutator,hYm,←Z_act,hZm] at hh
    exact hh
  have hzero' : ⁅Y',Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hzero
    rw [map_commutator,hYm,Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,
      ←Z_act,hQm,Subgroup.map_bot] at hh
    exact hh
  have hnle : ¬ Y ≤ Y' := fun hh =>
    hbad ((commutator_mono hh le_rfl).trans hcontrol')
  have hmove : x ∉ normalizer (Y : Set (FreeAmalgam Rg)) := by
    intro hn
    have he := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Y : Set (FreeAmalgam Rg))).inv_mem hn)
    exact hnle (he.symm.trans hYm).le
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    (selected_span_le_forward_kernel (h := h) hb p).trans
      (inf_le_left.trans (show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hx => hx.1))
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hpos : 0 < Y.relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hidx : Y.relIndex P ≤ 2 := by
    rw [inf_relIndex_left]
    exact (selected_span_index_of_forward_slice h e hz hk hb p hforward).2
  have hidxeq : Y'.relIndex P = Y.relIndex P := by
    calc
      _ = (Y.map (MulAut.conj x⁻¹).toMonoidHom).relIndex
          (P.map (MulAut.conj x⁻¹).toMonoidHom) := by rw [hYm,hPm]
      _ = _ := relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective
  have hidx' : Y.relIndex P = 2 := by
    have hh : Y.relIndex P ≠ 1 := by
      intro he
      exact hnle (inf_le_left.trans (relIndex_eq_one.mp (hidxeq.trans he)))
    omega
  have hidx'' : Y'.relIndex P = 2 := hidxeq.trans hidx'
  have hnle' : ¬ Y' ≤ Y := by
    intro hh
    have hi := relIndex_mul_relIndex Y' Y P hh inf_le_left
    rw [hidx',hidx''] at hi
    exact hnle (relIndex_eq_one.mp (show Y'.relIndex Y = 1 by omega))
  have hjoin : Y ⊔ Y' = P := by
    have hle : Y ⊔ Y' ≤ P := sup_le inf_le_left inf_le_left
    have hi := relIndex_mul_relIndex Y (Y ⊔ Y') P le_sup_left hle
    rw [hidx'] at hi
    have hp : 0 < (Y ⊔ Y').relIndex P := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : Y.relIndex (Y ⊔ Y') ≠ 1 := by
      intro he
      exact hnle' (le_sup_right.trans (relIndex_eq_one.mp he))
    have hj : (Y ⊔ Y').relIndex P = 1 := by
      have hd : (Y ⊔ Y').relIndex P ∣ 2 :=
        ⟨Y.relIndex (Y ⊔ Y'),by simpa only [Nat.mul_comm] using hi.symm⟩
      have hchoices := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd
      rcases hchoices with he | he
      · exact he
      · rw [he] at hi
        omega
    exact le_antisymm hle (relIndex_eq_one.mp hj)
  have hinter : (Y ⊓ Y').relIndex P = 4 := intersection_index_four P Y Y'
    inf_le_left inf_le_left hidx' hidx'' (fun he => hnle he.le)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    have hs := critical_predecessor_small_slice h e hz hk hb p
      (by simpa only [hl,Nat.reduceSub] using hopposite)
    rw [hs.2.2]
    decide
  have hnon := plane_four_selected_span_nonabelian_of_slices h e hz hk u hR hb4 p
    hforward hopposite
  have hcard : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 :=
    (small_selected_span_derived h e hz hk hb p hsmall hforward hnon).2.1
  have hderived := selected_span_derived_transfer h e hz hk hb p hcard Y inf_le_left
    (by rw [hidx'])
  have hderived' := selected_span_derived_transfer h e hz hk hb p hcard Y' inf_le_left
    (by rw [hidx''])
  exact ⟨t,hat,r,hr,q,hq,hgen,hpair,hnorm,hinside,hYm,hmove,hnle,hnle',hjoin,
    hidx',hidx'',hinter,hderived,hderived',hcard,hzero,hcontrol,hzero',hcontrol',hbad⟩

omit hk in
include h e hz in
/-- Whole-core application of the literal paired-midpoint kernel calculation.
The original switch, both generation identities and both covers are retained. -/
theorem coreExhaustion_or_cubic_plane_kernel_separation :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 → ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg z) ≤ 2 →
          let c := p.walk.getVert 2
          let P := localZSpan Rg c (alpha Rg)
          let Y := P ⊓ Q Rg c
          ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
            let x := (embedM Rg r)⁻¹
            let Y' := P ⊓ Q Rg (act Rg x c)
            ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
              (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
              (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) =
                stabilizer Rg (alpha Rg) ∧
              edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
                stabilizer Rg (alpha Rg) ∧
              x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
                Set (FreeAmalgam Rg)) ∧
              Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
              Y.map (MulAut.conj x⁻¹).toMonoidHom = Y' ∧
              x ∉ normalizer (Y : Set (FreeAmalgam Rg)) ∧
              ¬ Y ≤ Y' ∧ ¬ Y' ≤ Y ∧ Y ⊔ Y' = P ∧
              Y.relIndex P = 2 ∧ Y'.relIndex P = 2 ∧ (Y ⊓ Y').relIndex P = 4 ∧
              ⁅Y,Y⁆ = ⁅P,P⁆ ∧ ⁅Y',Y'⁆ = ⁅P,P⁆ ∧
              Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
              ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧
              ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
              ⁅Y',Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧
              ⁅Y',Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) ∧
              ¬ ⁅Y,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg))) := by
  rcases coreExhaustion_or_cubic_plane_terminal_slices h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 z p hf ho =>
        plane_four_selected_kernel_separation h e hz hk u hplane hb4 p hf ho⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the original same-switch kernel separation. -/
theorem rankTwo_or_cubic_plane_kernel_separation :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 → ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg z) ≤ 2 →
          let c := p.walk.getVert 2
          let P := localZSpan Rg c (alpha Rg)
          let Y := P ⊓ Q Rg c
          ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
            let x := (embedM Rg r)⁻¹
            let Y' := P ⊓ Q Rg (act Rg x c)
            ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
              (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
              (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) =
                stabilizer Rg (alpha Rg) ∧
              edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
                stabilizer Rg (alpha Rg) ∧
              x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
                Set (FreeAmalgam Rg)) ∧
              Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
              Y.map (MulAut.conj x⁻¹).toMonoidHom = Y' ∧
              x ∉ normalizer (Y : Set (FreeAmalgam Rg)) ∧
              ¬ Y ≤ Y' ∧ ¬ Y' ≤ Y ∧ Y ⊔ Y' = P ∧
              Y.relIndex P = 2 ∧ Y'.relIndex P = 2 ∧ (Y ⊓ Y').relIndex P = 4 ∧
              ⁅Y,Y⁆ = ⁅P,P⁆ ∧ ⁅Y',Y'⁆ = ⁅P,P⁆ ∧
              Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
              ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧
              ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
              ⁅Y',Z Rg (act Rg x z) ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧
              ⁅Y',Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) ∧
              ¬ ⁅Y,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg))) :=
  (coreExhaustion_or_cubic_plane_kernel_separation h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
