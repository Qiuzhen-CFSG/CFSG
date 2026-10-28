module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Cover
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Flags
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Structure

/-!
# Centralizer-seed deductions for 13.8.6(5)

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.948.

The five-dimensional augmentation cover determines the actual centralizer
seed: its image is the constant line, its relative index modulo V is two,
and [L₁T,U₁] ≤ V₁. These facts are derived using an equivariant identification
of the literal UH/V₁ and the earlier weight-four flag, not an assumed fixed
spanning vector or permutation quotient. The original natural L-module
identification separately proves V = ⟨V₁^L⟩.

The normalization and quotient lemmas derive relative normality, elementary
abelianness, and the actor-kernel commutator bound. They permit nonabelian U_L.
The actor comparison uses precisely MV/C_MV(V) from Notation 12.2.5(2).

Source assembly still requires the coordinate marking of the image of L₁T
as an actual unordered-pair stabilizer, retaining a possible outer twist,
and applicability of the earlier containment C_LT(V) ≤ T. These obligations
are not asserted by the conditional deductions exported here. The fixed
seed, spanning orbit and permutation surjection are assembled by Quotients.
-/
