/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable singletons in a sum of measurable spaces

Mathlib provides the measurable space `α ⊕ β` but no `MeasurableSingletonClass` instance for it.
This file adds it (a candidate for upstreaming to Mathlib).

## Main statements

* `Sum.instMeasurableSingletonClass`: if `α` and `β` have measurable singletons, so does `α ⊕ β`.
-/

@[expose] public section

/-- A sum of measurable spaces with measurable singletons has measurable singletons. -/
instance Sum.instMeasurableSingletonClass {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a =>
      rw [← Set.image_singleton]
      exact (measurableSet_singleton a).inl_image
    | inr b =>
      rw [← Set.image_singleton]
      exact (measurableSet_singleton b).inr_image
