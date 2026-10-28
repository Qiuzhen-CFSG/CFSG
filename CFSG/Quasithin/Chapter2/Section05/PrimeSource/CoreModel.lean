module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EarlyCoreSource

/-!
# The original prime core is nonabelian dihedral

The quotient model identifies the image of the original Sylow subgroup
with a dihedral group. The proved faithful embedding of the crossing core
then makes the core cyclic or dihedral. The original abelian-core exclusion
removes the cyclic and four-group cases, giving the literal dihedral model
used by the prime involution-fixed generation theorem.

Source: Aschbacher--Smith 2.5.21, printed pp.565--566.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The PSL quotient gives the actual nonabelian core its dihedral model. -/
theorem MathieuSourceSetup.psl_nonabelian_twoCore_model
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    {F : Type*} [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eQ : (H ⧸ pCore 2 H) ≃* PSL(2,F))
    (hn : ¬ IsMulCommutative (twoCore H)) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  obtain ⟨f,hf,hker⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨x,hxT,hxS,hxN,hx2⟩ := exists_outside_normalizer_square_mem
    ((S : Subgroup H).map H.subtype) (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  obtain ⟨n,_,⟨eP⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd
    (S.mapSurjective hf)
  obtain hc | ⟨k,⟨e⟩⟩ := MathieuSourceSetup.twoCore_cyclic_or_dihedral
    c hgen f hker x hxT hxS hxN hx2 eP
  · exact (hn hc.isMulCommutative).elim
  refine ⟨k,?_,⟨e⟩⟩
  by_contra! hk
  have hh : IsMulCommutative (DihedralGroup (2 ^ k)) := by
    apply DihedralGroup.commutative_iff.mpr
    interval_cases k <;> decide
  exact hn ⟨⟨fun a b => e.injective
    (by simpa only [map_mul] using hh.is_comm.comm (e a) (e b))⟩⟩

/-- The prime source's actual quotient and abelian-core exclusion discharge
the actor-shape input of its involution-fixed generation theorem. -/
theorem MathieuSourceSetup.prime_source_twoCore_model
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p))
    (hQ : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(2,ZMod p)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p)))
    (hlarge : 2 < Nat.card (twoCore H)) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  have ho : Odd p := hfm.1.odd_of_ne_two (by omega)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,Fact.out,ho,by decide,by simp⟩
  rcases hQ with hQ | hQ
  · obtain ⟨eQ⟩ := hQ
    exact MathieuSourceSetup.psl_nonabelian_twoCore_model c hgen hodd eQ
      (MathieuSourceSetup.prime_psl_source_twoCore_noncommutative
        c hG hempty hgen hb hp hfm eK eQ hlarge)
  · obtain ⟨eQ⟩ := hQ
    exact MathieuSourceSetup.pgl_nonabelian_twoCore_model c hgen hodd eQ
      (MathieuSourceSetup.prime_pgl_source_twoCore_noncommutative
        c hG hempty hgen hb hp hfm eK eQ hlarge)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
