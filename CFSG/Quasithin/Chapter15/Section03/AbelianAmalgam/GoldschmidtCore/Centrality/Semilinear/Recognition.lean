module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.QuotientMarking
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Conjugation
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.TerminalComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelExclusions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.LinearTwoSylow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FinalComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceKernel

/-!
# Conditional natural-module recognition for the bad-character branch

The complete universal F.6.18 and B.5.6 implications, together with the
actual terminal configuration, faithful binary quotient action and supplied
offender-image containment, imply H/O₂(H) ≃ SL₃(2). The comparison proves
that the actual offender subgroup is the whole quotient. It retains the full
B.5 module conclusion and eliminates every incompatible F.6.18 alternative
using actual cubic sections, Sylow structures and model order comparisons.

The four-group F = ⟨Z^{Y_F}⟩ lies in the actual span W = ⟨Zᴴ⟩. The first
local group preserves F and the second centralizes Z = Ω₁Z(T), of order two.
A faithful action agreeing literally with ambient conjugation then identifies
W with the natural binary three-space under one compatible marking of the
common Sylow, G₁ as the line stabilizer, and G₂ as the point stabilizer.
Every nonzero orbit has seven vectors. The compatible external quotient
also makes the literal intersection G₁ ∩ K maximal of index seven in K.

The full universal classification implications remain explicit parent inputs;
this module does not prove either source classification or 15.3.68(2).
The parent also supplies the actual action, span and offender containment,
and constructs the doubled-natural module and final ambient identification.
No dimension, irreducibility, common-core equality or centrality-based strict
local-core bound is assumed. The earlier recognition-conditional public API
is preserved alongside the new full conditional assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1152–1155; classification inputs F.6.18, pp.309–310, and B.5.3/B.5.6,
pp.104–105. The parent retains construction of W, its faithful action, the
conjugation identity, the offender transfer, and final ambient assembly.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- In the actual terminal configuration, one quotient marking identifies the
common Sylow, both local parabolics, and the actual conjugation representation.
Recognition of the quotient and construction of the faithful action remain
explicit inputs. -/
theorem terminal_natural_of_recognition
    (T : Sylow 2 G) (M Y V E F W : Subgroup G) [IsElementaryAbelian 2 W]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hZE : centralInvolutions T ≤ E) (hZ : Nat.card (centralInvolutions T) = 2)
    (hspan : W = conjugateSpanBy (centralInvolutions T) (amalgamGroup Y T E F))
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) (Additive W))
    (hfaith : Function.Injective ρ)
    (hconj : ∀ (h : amalgamGroup Y T E F) (w : Additive W),
      ((ρ (QuotientGroup.mk' _ h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (e₀ : (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≃*
      Matrix.PSL3Two.PSL) :
    ∃ m : (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≃* Matrix.PSL3Two.SL,
      ((lineT T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL ∧
      ((firstAmalgamGroup Y T E F).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL ∧
      ((secondAmalgamGroup T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL ∧
      Nonempty (ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) := by
  let H := amalgamGroup Y T E F
  let G₁ := firstAmalgamGroup Y T E F
  let G₂ := secondAmalgamGroup T E
  have hZW : centralInvolutions T ≤ W := by rw [hspan]; exact le_conjugateSpanBy _ _
  have hNW : H ≤ normalizer (W : Set G) := by
    rw [hspan]; exact le_normalizer_conjugateSpanBy _ _
  have hFW : F ≤ W := by
    rw [c.seed_span]
    apply iSup_le
    intro y
    have hy : lineY Y F ≤ H := le_sup_left.trans le_sup_left
    rintro x ⟨z,hz,rfl⟩
    exact le_normalizer_iff.mp hNW _
      (show (y : G)⁻¹ ∈ H from H.inv_mem (hy y.property))
      _ (hZW hz)
  have h₁ : G₁ ≤ normalizer (F : Set G) := by
    apply sup_le ((lineY_le Y F).trans inf_le_right)
    rw [← c.lineT_eq]
    exact inf_le_right
  have h₂ : G₂ ≤ centralizer (centralInvolutions T : Set G) :=
    sup_le ((lineX_le_centralizer E).trans (centralizer_le hZE))
      (inf_le_left.trans (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)))
  obtain ⟨S,m,hS,hB,hm₁,hm₂⟩ := mark_goldschmidt_quotient
    (G₁.subgroupOf H) (G₂.subgroupOf H) c.goldschmidt e₀
  have hs : (lineT T E).subgroupOf H = (S : Subgroup H) := by
    rw [← c.intersection]
    exact hS
  have hm₁' : (G₁.subgroupOf H).map (m.toMonoidHom.comp (QuotientGroup.mk' _)) =
      Matrix.PSL3Two.lineParabolicSL := by rw [← map_map]; exact hm₁
  have hm₂' : (G₂.subgroupOf H).map (m.toMonoidHom.comp (QuotientGroup.mk' _)) =
      Matrix.PSL3Two.pointParabolicSL := by rw [← map_map]; exact hm₂
  refine ⟨m,?_,hm₁',hm₂',?_⟩
  · rw [hs,← map_map]; exact hB
  · exact natural_of_conjugation_marking H (centralInvolutions T) F W G₁ G₂
      (QuotientGroup.mk' _) ρ hfaith hconj c.seed_le hFW hZ c.line_card
      hspan h₁ h₂ m hm₁' hm₂'


open Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- From the full universal source implications, the actual conjugation
module has one compatible Sylow/line/point marking and is the natural module.
Every nonzero orbit has seven vectors, including the nonzero vector of Z.
No quotient recognition, dimension or irreducibility premise is assumed. -/
theorem terminal_natural_of_full_classifications {K : GroupClass}
    (sourceF : FSource.ClassificationInput K) (sourceB : GeneralClassificationInput.{u,u} K)
    (T : Sylow 2 G) (M Y V E F W : Subgroup G) [IsElementaryAbelian 2 W]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    (hZE : centralInvolutions T ≤ E) (hZ : Nat.card (centralInvolutions T) = 2)
    (hspan : W = conjugateSpanBy (centralInvolutions T) (amalgamGroup Y T E F))
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) (Additive W))
    (hfaith : Function.Injective ρ)
    (hconj : ∀ (h : amalgamGroup Y T E F) (w : Additive W),
      ((ρ (QuotientGroup.mk' _ h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ)
    (hr : primeRank 3 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≤ 1) :
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧ offenderSubgroup ρ = ⊤ ∧
    ∃ m : (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≃* Matrix.PSL3Two.SL,
      ((lineT T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL ∧
      ((firstAmalgamGroup Y T E F).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL ∧
      ((secondAmalgamGroup T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL ∧
      Nonempty (ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) ∧
      ∀ z : Additive W, z ≠ 0 → Nat.card (Set.range (fun g => ρ g z)) = 7 := by
  obtain ⟨hb, hi, ⟨e⟩⟩ := terminal_recognition_of_full_classifications (G := G) (W := Additive ↥W) sourceF sourceB
    T M Y V E F d c hH hTM hX ρ hfaith hXI hr
  obtain ⟨m, hS, h₁, h₂, ⟨a⟩⟩ := terminal_natural_of_recognition
    T M Y V E F W d c hZE hZ hspan ρ hfaith hconj (e.trans Matrix.PSL3Two.equiv)
  exact ⟨hb, hi, m, hS, h₁, h₂, ⟨a⟩, fun z hz => quotient_natural_orbit_card ρ m a z hz⟩

/-- The same marking also proves maximality and index seven for the literal
intersection G₁ ∩ K_external. The independent quotient witness is explicit,
including compatibility of its quotient map with ambient membership. -/
theorem terminal_natural_and_external_index_seven {K : GroupClass}
    (sourceF : FSource.ClassificationInput K) (sourceB : GeneralClassificationInput.{u,u} K)
    (T : Sylow 2 G) (M Y V E F W : Subgroup G) [IsElementaryAbelian 2 W]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    (hZE : centralInvolutions T ≤ E) (hZ : Nat.card (centralInvolutions T) = 2)
    (hspan : W = conjugateSpanBy (centralInvolutions T) (amalgamGroup Y T E F))
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) (Additive W))
    (hfaith : Function.Injective ρ)
    (hconj : ∀ (h : amalgamGroup Y T E F) (w : Additive W),
      ((ρ (QuotientGroup.mk' _ h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ)
    (hr : primeRank 3 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≤ 1)
    (Kexternal : Subgroup G) (N : Subgroup Kexternal) [N.Normal]
    (e : (Kexternal ⧸ N) ≃*
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)))
    (hcompat : ∀ k : Kexternal,
      e (QuotientGroup.mk' N k) ∈
        ((firstAmalgamGroup Y T E F).subgroupOf (amalgamGroup Y T E F)).map
          (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ↔
        (k : G) ∈ firstAmalgamGroup Y T E F) :
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧ offenderSubgroup ρ = ⊤ ∧
    ∃ m : (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≃* Matrix.PSL3Two.SL,
      ((lineT T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL ∧
      ((firstAmalgamGroup Y T E F).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL ∧
      ((secondAmalgamGroup T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL ∧
      Nonempty (ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) ∧
      (∀ z : Additive W, z ≠ 0 → Nat.card (Set.range (fun g => ρ g z)) = 7) ∧
      IsCoatom (((firstAmalgamGroup Y T E F) ⊓ Kexternal).subgroupOf Kexternal) ∧
      ((firstAmalgamGroup Y T E F) ⊓ Kexternal).relIndex Kexternal = 7 := by
  obtain ⟨hb, hi, m, hS, h₁, h₂, ha, ho⟩ := terminal_natural_of_full_classifications
    sourceF sourceB T M Y V E F W d c hH hTM hX hZE hZ hspan ρ hfaith hconj hXI hr
  have hext := actual_intersection_maximal_index_seven (amalgamGroup Y T E F)
    Kexternal (firstAmalgamGroup Y T E F) N (pCore 2 (amalgamGroup Y T E F)) e m
    (by rw [map_map]; exact h₁) hcompat
  exact ⟨hb, hi, m, hS, h₁, h₂, ha, ho, hext⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
