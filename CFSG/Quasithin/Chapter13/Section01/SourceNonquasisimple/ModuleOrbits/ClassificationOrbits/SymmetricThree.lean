module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.MarkedConsumers

/-!
# The actual symmetric-three quotient in the deleted S5 branch

The selected component stabilizer has its proved S3 quotient under the
original LT marking. The odd Frattini kernel lies in the solvable radical,
which is the kernel of that component marking. Hence the point-stabilizer
quotient descends through the literal odd Frattini action, with both maps
retained. This supplies the symmetric-three clause used by the centralizer
sieve. The deleted-module Sylow reducibility argument remains separate.

Source: Aschbacher--Smith, proof of 13.1.12, pp.873--874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The S3 quotient is of the original odd Frattini action image. -/
theorem SymmetricFiveMarking.symmetricThreeStabilizerQuotient
    (d : SymmetricFiveMarking T L) (h : Context T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    SymmetricThreeStabilizerQuotient L p u := by
  obtain ⟨e⟩ := ((d.centralizer_orbit h.hypothesis h.maximal h.nonquasisimple
    ⟨u,s.mem⟩ (fun he => s.ne_one (congrArg Subtype.val he)) s.local_sylow).2 hnt).1
  let C := L ⊓ centralizer ({u} : Set G)
  let J := L ⊔ (T : Subgroup G)
  let i : C →* J := inclusion (inf_le_left.trans le_sup_left)
  let A := (C.subgroupOf J).map d.quotient
  let q : C →* A := (d.quotient.comp i).codRestrict A (fun c =>
    ⟨i c,c.property,rfl⟩)
  have hq : Function.Surjective q := by
    rintro ⟨a,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,Subtype.ext rfl⟩
  let ρ := componentStabilizerFrattiniAction L p u
  have hk : ρ.rangeRestrict.ker ≤ q.ker := by
    intro c hc
    have he : ρ c = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
    have hl : inclusion (show C ≤ L from inf_le_left) c ∈ solvableRadical L := by
      apply component_frattini_kernel_le_radical h.hypothesis.simpleQTKE h.maximal.1.1
        h.nonquasisimple h.odd h.divides
      rw [MonoidHom.mem_ker]
      exact (xiFrattiniAction_restrict inf_le_left (XiP_invariant p L.le_normalizer) c).symm.trans he
    have hq1 := MonoidHom.mem_ker.mp
      ((d.component_kernel_eq_radical h.hypothesis h.many h.maximal h.nonquasisimple).symm ▸ hl)
    apply MonoidHom.mem_ker.mpr
    exact Subtype.ext hq1
  let f : ρ.range →* A := ρ.rangeRestrict.liftOfSurjective
    ρ.rangeRestrict_surjective ⟨q,hk⟩
  have hf (c : C) : f (ρ.rangeRestrict c) = q c := by
    simp [f]
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨c,rfl⟩ := hq a
    exact ⟨ρ.rangeRestrict c,hf c⟩
  exact ⟨e.toMonoidHom.comp f,e.surjective.comp hs⟩

/-- The literal second classification row discharges the symmetric-three
premise in the source centralizer sieve. -/
theorem Classification.SymmetricFiveRow.symmetricThreeStabilizerQuotient
    (d : Classification.SymmetricFiveRow T L) (h : Context T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    SymmetricThreeStabilizerQuotient L p u :=
  d.marking.symmetricThreeStabilizerQuotient h s hnt

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
