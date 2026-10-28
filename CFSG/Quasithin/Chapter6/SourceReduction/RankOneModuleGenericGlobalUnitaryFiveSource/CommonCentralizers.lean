module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.NativeInvolutions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OddCore
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.Amalgam.CentralizerControl
public import Theory.GroupTheory.CentralizerPairTransport

/-!
# Common ambient centralizers at the marked U₅(4) short root

The selected short involution lies in the original S and hence in the whole
normalizer overlap. Its full-extension centralizer lies in the plane
endpoint. Transport through the two full endpoints therefore puts
N_G(residual H) ∩ C_G(t) inside N_G(L). The original long-root TI group
Z(residual H) then gives normalizer control for all its nontrivial subgroups
inside C_G(t), and full common-centralizer control for its nonidentity
points. The same holds on every conjugate of this line by the local
short centralizer. The original full common-centralizer orders are computed
through the identical full endpoint equivalence. The original long-root
line lies in the local short centralizer, and the full short centralizer has
trivial odd core by the ambient Klein-four argument.

Both orientations, all range equations, the same lift and its whole-D action
are retained. The long-root line here is Z(residual H), distinct from the
short fixed line C_V(K_t) in the later quotient argument. This is an input
to F.4.42's orbit comparison; it does not assert unique fixed cosets or the
full containment C_G(t) ≤ N_G(L). S=T and the final order comparison also
remain separate steps.
Source: Aschbacher--Smith F.4.34,42, printed pp.291,295--296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The marked short root has full common-centralizer and root-normalizer
control on the original long-root line, with its actual endpoint counts. -/
theorem Preparation.unitaryFive_marked_short_root_control
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      ∃ t : (normalizerAmalgam L (residual H)).M₁₂,
        t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
        orderOf t.val = 2 ∧ t.val ∈ sourceS L H ∧
        (center (residual H)).map (residual H).subtype ≤
          normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G) ∧
        pPrimeCore 2 (centralizer ({t.val} : Set G)) = ⊥ ∧
        (F.middle t).val = MulAut.conj U.shortInvolution.val ∧
        centralizer ({inclusion (inf_le_left.trans r.extension.left_le) (F.middle t)} :
          Set r.extension.carrier) ≤ r.extension.right.subgroupOf r.extension.carrier ∧
        Nat.card (centralizer ({inclusion inf_le_left t} : Set (normalizer (L : Set G)))) =
          Nat.card (centralizer ({inclusion (inf_le_left.trans r.extension.left_le) (F.middle t)} :
            Set r.extension.carrier)) ∧
        (normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G) ≤
          normalizer (L : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype → B ≠ ⊥ →
          normalizer (B : Set G) ⊓ centralizer ({t.val} : Set G) ≤
            normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)) ∧
        (∀ z : G, z ∈ (center (residual H)).map (residual H).subtype → z ≠ 1 →
          centralizer ({z} : Set G) ⊓ centralizer ({t.val} : Set G) ≤
            (normalizerAmalgam L (residual H)).M₁₂) ∧
        (∀ g ∈ normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G),
          ∀ B : Subgroup G,
            B ≤ ((center (residual H)).map (residual H).subtype).map (MulAut.conj g).toMonoidHom →
            B ≠ ⊥ → normalizer (B : Set G) ⊓ centralizer ({t.val} : Set G) ≤
              normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)) ∧
        (∀ g ∈ normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G),
          ∀ z : G,
            z ∈ ((center (residual H)).map (residual H).subtype).map (MulAut.conj g).toMonoidHom →
            z ≠ 1 → centralizer ({z} : Set G) ⊓ centralizer ({t.val} : Set G) ≤
              normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)) ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → z.val ≠ 1 →
          Nat.card (centralizer ({z.val} : Set G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
            Nat.card (centralizer ({F.right z} : Set r.extension.left) ⊓
              centralizer ({F.right (inclusion inf_le_right t)} : Set r.extension.left) :
                Subgroup r.extension.left)) := by
  obtain ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,_,p,hpZ,hp2,hpshort,hfull,hcard⟩ :=
    d.unitaryFive_marked_native_involutions h hH hp U hc r
  have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hE => hE.1
  have hpT : p.val ∈ (T : Subgroup G) :=
    hJT ((d.unitaryFive_thompson h hH hp U hc).ge hpZ)
  have hpR : p.val ∈ (T : Subgroup G) ⊓ L :=
    ⟨hpT,(pCoreIn_le 2 L) (map_subtype_le _ hpZ)⟩
  have hpS : p.val ∈ sourceS L H :=
    (d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc).ge hpR
  have hp1 : p.val ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 :=
    (show (T : Subgroup G) ⊓ L ≤ _ from le_sup_right.trans le_sup_left) hpR
  let t : (normalizerAmalgam L (residual H)).M₁₂ :=
    ⟨p.val,r.left_le p.property,r.right_le hp1⟩
  have hmark : (F.middle t).val = (F.left (inclusion r.left_le p)).val :=
    (congrArg Subtype.val (F.left_commutes t)).symm
  have hshort : (F.middle t).val = MulAut.conj U.shortInvolution.val := by
    rw [hmark,h0,hpshort]
  have hcarrier : inclusion (inf_le_left.trans r.extension.left_le) (F.middle t) =
      inclusion r.extension.right_le (F.left (inclusion r.left_le p)) := Subtype.ext hmark
  have hcross : normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G) ≤
      normalizer (L : Set G) := by
    apply F.centralizer_right_le_left_of_overlap (h₀ := inf_le_right) (h₁ := inf_le_left)
      (inf_comm _ _) t
    intro x hx
    let y : r.extension.carrier := ⟨x,r.extension.left_le hx.1⟩
    apply hfull (show y ∈ centralizer
      ({inclusion r.extension.right_le (F.left (inclusion r.left_le p))} :
        Set r.extension.carrier) from ?_)
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
  have htK : t.val ∈ residual H :=
    ((d.common_sylow_of_comparison h hH.1.1.2 hp (.unitaryFive U hc)).le hpR).2
  have hZt : (center (residual H)).map (residual H).subtype ≤
      centralizer ({t.val} : Set G) := by
    rintro z ⟨v,hv,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (residual H).subtype (mem_center_iff.mp hv ⟨t.val,htK⟩)).symm
  have hZlocal : (center (residual H)).map (residual H).subtype ≤
      normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G) := by
    refine le_inf (fun z hz => hcross ⟨?_,hZt hz⟩) hZt
    exact (residual H).le_normalizer (map_subtype_le _ hz)
  have hodd := d.unitaryFive_involution_centralizer_oddCore h hH hp U hc t.val hp2
  obtain ⟨_,hTI,hN⟩ := d.unitaryFive_right_center_fusion h hH hp U hc
  have hcz (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype)
      (hz1 : z ≠ 1) : centralizer ({z} : Set G) ≤ normalizer (residual H : Set G) :=
    (hTI.centralizer_le_normalizer hz hz1).trans_eq hN
  have hroot : normalizer ((center (residual H)).map (residual H).subtype : Set G) ⊓
      centralizer ({t.val} : Set G) ≤ normalizer (L : Set G) := by
    rw [hN]
    exact hcross
  refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,t,hpZ,hp2,hpS,hZlocal,hodd,hshort,
    hcarrier.symm ▸ hfull,hcarrier.symm ▸ hcard,hcross,?_,?_,?_,?_,?_⟩
  · intro B hBZ hB
    have hBN : normalizer (B : Set G) ≤ normalizer (residual H : Set G) :=
      (hTI.normalizer_le_of_ne_bot hB hBZ).trans_eq hN
    exact le_inf ((inf_le_inf_right _ hBN).trans hcross) inf_le_right
  · intro z hz hz1
    exact le_inf ((inf_le_inf_right _ (hcz z hz hz1)).trans hcross)
      (inf_le_left.trans (hcz z hz hz1))
  · intro g hg B hBZ hB
    have hNg := normalizer_inf_centralizer_conjugate_le hroot hg.1 hg.2
    have hBN := (hTI.map_equiv (MulAut.conj g)).normalizer_le_of_ne_bot hB hBZ
    exact le_inf ((inf_le_inf_right _ hBN).trans hNg) inf_le_right
  · intro g hg z hz hz1
    have hNg := normalizer_inf_centralizer_conjugate_le hroot hg.1 hg.2
    have hzN := (hTI.map_equiv (MulAut.conj g)).centralizer_le_normalizer hz hz1
    exact le_inf ((inf_le_inf_right _ hzN).trans hNg) inf_le_right
  · intro z hz hz1
    exact Nat.card_congr (pairCentralizerEquiv _ F.right z (inclusion inf_le_right t)
      (inf_le_left.trans (hcz z hz hz1))).toEquiv

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
