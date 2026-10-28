module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.SylowFacts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.OddComplement

/-!
# The two-central five-family from the marked root-five family

Sylow conjugacy in the involution centralizer makes the two-central family
one conjugacy class. Thus one actual D₁₀ × D₁₀ normalizer supplies every
normalizer in that family. The root-family normalizers have order 600,
whereas the two-central normalizers have order 100, proving separation.
The root-family product model independently supplies elementary abelianness
and self-centralization of every Sylow five-subgroup.

The final theorem chooses a root-family member E in a Sylow subgroup P.
`MarkedLocal` constructs `TwoCentral.LocalData` for the literal intersection
P ∩ E(C_G(E)), retaining the component and inverter from the root witness.
`OddComplement` then proves the representative normalizer by the normal
odd-complement and inversion argument. Thus all local and global premises
of the intermediate assembly are discharged. Only the root-five family
remains an explicit input, to be supplied by the full 47.2 assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal

variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_equiv_of_twoCentral_representative (D : Seed G)
    (Y : Subgroup G) (hY : FiveCentralizing D.z Y)
    (eY : normalizer (Y : Set G) ≃* (DihedralGroup 5 × DihedralGroup 5))
    (F : Subgroup G) (hF : FiveCentralizing D.z F) :
    Nonempty (normalizer (F : Set G) ≃* (DihedralGroup 5 × DihedralGroup 5)) := by
  obtain ⟨A, _, _, hA⟩ := twoCentral_five_orbit D
  obtain ⟨a, ha⟩ := (hA Y).mp hY
  obtain ⟨b, hb⟩ := (hA F).mp hF
  have hg : (b * a⁻¹) • Y = F := by
    rw [← ha, mul_smul, inv_smul_smul]
    exact hb
  let e := MulAut.conj (ConjAct.ofConjAct (b * a⁻¹))
  have hm : Y.map e.toMonoidHom = F := hg
  have hn : (normalizer (Y : Set G)).map e.toMonoidHom = normalizer (F : Set G) := by
    rw [map_equiv_normalizer_eq, hm]
  exact ⟨(((normalizer (Y : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hn)).symm.trans eY⟩

/-- A single proved two-central normalizer supplies the full branch. Its existence
is an explicit remaining premise, not an assumption of source 47.2. -/
theorem twoCentralFiveFamily_of_representative {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (Y : Subgroup G) (hY : FiveCentralizing D.z Y)
    (hNY : Nonempty (normalizer (Y : Set G) ≃* (DihedralGroup 5 × DihedralGroup 5))) :
    TwoCentralFiveFamily D S.t := by
  obtain ⟨eY⟩ := hNY
  have hB := normalizer_equiv_of_twoCentral_representative D Y hY eY
  exact {
    normalizer := hB
    separated := by
      intro E hE hEB
      obtain ⟨W⟩ := hA E hE
      obtain ⟨eB⟩ := hB E hEB
      have ha := Nat.card_congr W.equiv.toEquiv
      have hb := Nat.card_congr eB.toEquiv
      rw [Nat.card_prod, DihedralGroup.nat_card, InvolutionGeometry.card_A5] at ha
      rw [Nat.card_prod, DihedralGroup.nat_card] at hb
      omega
    elementary := fun P => (TwoCentral.sylow_facts_of_root_family hG S hA P).1
    self_centralizing := fun P => (TwoCentral.sylow_facts_of_root_family hG S hA P).2 }

/-- The actual intersection and the marked inverter put the representative in
the required family. The local-to-global normalizer implication remains explicit. -/
theorem twoCentralFiveFamily_of_local_calculation {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) {E : Subgroup G} (W : RootFiveWitness D E)
    (P : Sylow 5 G)
    (L : TwoCentral.LocalData E ((P : Subgroup G) ⊓ fiveComponent E) P W.inverter)
    (hglobal : ∀ (E Y : Subgroup G) (P : Sylow 5 G) (z : G),
      TwoCentral.LocalData E Y P z → IsElementaryAbelian 5 P →
      centralizer (P : Set G) = (P : Subgroup G) →
      Nonempty (normalizer (Y : Set G) ≃* (DihedralGroup 5 × DihedralGroup 5))) :
    TwoCentralFiveFamily D S.t := by
  have hP := TwoCentral.sylow_facts_of_root_family hG S hA P
  exact twoCentralFiveFamily_of_representative hG S hA _
    ⟨L.card_Y, W.inverter, W.inverter_conj, L.centralizes_Y⟩
    (hglobal E _ P W.inverter L hP.1 hP.2)

/-- The marked root-five family implies all four conclusions of the two-central
branch of 47.2: the actual D₁₀ × D₁₀ normalizers, separation from the root-four
family, and elementary abelianness and self-centralization of every Sylow
five-subgroup. The literal intersection and its local-to-global normalizer
calculation are constructed here; neither remains an additional premise. -/
theorem twoCentralFiveFamily_of_root_family {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) : TwoCentralFiveFamily D S.t := by
  classical
  let P : Sylow 5 G := default
  obtain ⟨E, _, _, W, ⟨L⟩⟩ := TwoCentral.MarkedLocal.exists_localData hG S hA P
  exact twoCentralFiveFamily_of_local_calculation hG S hA W P L
    TwoCentral.OddComplement.normalizer_equiv

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
