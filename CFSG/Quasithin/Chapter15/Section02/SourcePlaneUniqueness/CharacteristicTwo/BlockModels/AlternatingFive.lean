module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.Orbits
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFivePlaneCentralizer

/-!
# The literal A5 block centralizer in the escaping-plane case

The original plane lies in the Sylow-fixed part of the ambient two-core.
The A5 block theorem therefore identifies its actual centralizer inside the
block as a Borel, and identifies the corresponding quotient subgroup as a
point stabilizer in the five-point action. The orbit module and its
fixed-codimension comparison for the offender argument remain separate.

Source: Aschbacher--Smith, 15.2.23, printed p.1115, and C.1.13(c),
printed pp.124--125; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original A5 block centralizer has its actual Borel marking. -/
theorem a5_block_borel_marking (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5)
    (hout : ¬ X.map I.subtype ≤ Mc) :
    let f := I.subtype.comp X.subtype
    (centralizer (ZS : Set G)).comap f = Mc.comap f ∧
      ∃ P : Sylow 2 X, ∃ e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
        ∃ i : Fin 5,
          (P : Subgroup X).map f = planeSylow T ZS ⊓ X.map I.subtype ∧
          Mc.comap f = normalizer (P : Set X) ∧
          Mc.comap f = (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) := by
  let f := I.subtype.comp X.subtype
  let W := ZS.subgroupOf I
  let J := Mc.comap f
  have hZI : ZS ≤ I := d.plane_le_centralizer.trans
    ((d.centralizer_le_intersection hI).trans inf_le_right)
  have hWQ : W ≤ pCore 2 I := by
    intro z hz
    have hzQ := ((mem_omegaOneCenterAmbient_iff _ _).mp
      (d.plane_le_escape_core_omega hI hfit hz)).1
    obtain ⟨q,hq,he⟩ := hzQ
    exact (Subtype.ext he : q = z) ▸ hq
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨P,hP⟩ := R.exists_subgroupOf_eq_of_subnormal X hX.subnormal
  have hWP : W ≤ centralizer ((P : Subgroup X).map X.subtype : Set I) := by
    rintro z hz p ⟨p,hp,rfl⟩
    apply Subtype.ext
    have hpR : (p : I) ∈ R := by
      change p ∈ (R : Subgroup I).subgroupOf X
      rwa [← hP]
    have hpS : ((p : I) : G) ∈ planeSylow T ZS :=
      hR ▸ mem_map_of_mem I.subtype hpR
    have hzS := (mem_omegaOneCenterAmbient_iff _ _).mp
      (d.omega_center ▸ (show (z : G) ∈ ZS from hz))
    exact hzS.2.2 p hpS
  have hJ : J ≠ ⊤ := by
    intro he
    apply hout
    rintro x ⟨x,hx,rfl⟩
    exact (show (⟨x,hx⟩ : X) ∈ J from he ▸ mem_top _)
  have hCW : (centralizer (W : Set I)).comap X.subtype =
      (centralizer (ZS : Set G)).comap f := by
    ext x
    constructor
    · intro hx z hz
      exact congrArg I.subtype (hx ⟨z,hZI hz⟩ hz)
    · intro hx z hz
      exact Subtype.ext (hx z hz)
  have hCJ : (centralizer (W : Set I)).comap X.subtype ≤ J := by
    rw [hCW]
    intro x hx
    exact ((d.centralizer_le_intersection hI) hx).1
  obtain ⟨hCJ_eq,hJN,e,i,hei⟩ := hb.centralizer_borel_of_sylow_fixed
    X hX P W hWQ hWP J hJ hCJ
  refine ⟨hCW.symm.trans hCJ_eq,P,e,i,?_,hJN,hei⟩
  rw [← map_map, hP, subgroupOf_map_subtype, map_inf _ _ _ I.subtype_injective, hR]

/-- The source orbit alternative discharges the properness premise of the Borel calculation. -/
theorem a5_block_borel_marking_of_source
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) :
    let f := I.subtype.comp X.subtype
    (centralizer (ZS : Set G)).comap f = Mc.comap f ∧
      ∃ P : Sylow 2 X, ∃ e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5),
        ∃ i : Fin 5,
          (P : Subgroup X).map f = planeSylow T ZS ⊓ X.map I.subtype ∧
          Mc.comap f = normalizer (P : Set X) ∧
          Mc.comap f = (MulAction.stabilizer (alternatingGroup (Fin 5)) i).comap
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) :=
  d.a5_block_borel_marking hI hfit hX hb
    (d.alternating_block_not_le_partner horbit hI hfit hX (Or.inl rfl) hb)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
